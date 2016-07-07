{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-type-defaults
                -fno-warn-missing-signatures
                -fno-warn-unused-do-bind
                -fno-warn-unused-imports
                -fno-warn-name-shadowing #-}

-- | Godel's T: a total language with natural numbers

module T1 where

import Prelude hiding (succ)
import qualified Data.Map as Map
import Data.Map (Map)

import Spec.T

data T1

instance SystemT T1 where

  type Syn T1 = Syntax

  ($:) = (:$:)
  zero = Z
  succ = S

  lam t f = Lam name t body
    where
      name = maxBV body + 1
      body = f (Var name)

  -- XXX:
  rec zero step arg =
    Rec zero (lam Nat $ \prev -> lam Nat $ \res -> step prev res) arg

  unnat = \case
    S n -> 1 + unnat n
    Z -> 0
    e -> error $ "unnat: can't eval: " ++ show e

  nat = \case
    0 -> Z
    k -> S (nat (k-1))

  typecheck = typecheck'
  beta = eval

-- * Syntax

type Name = Int

data Syntax
  = Var Name
  | Lam Name Type Syntax
  | Syntax :$: Syntax
  | Z
  | S Syntax
  | Rec Syntax Syntax Syntax
  deriving (Show, Eq)

-- Lambda calculus-style function application associates to the left.
infixl 2 :$:

-- | Axelsson & Claessen, Using Circular Programs for Higher-Order Syntax.
maxBV :: Syntax -> Int
maxBV = \case
  Var _             -> 0
  Lam n _ _         -> n
  f :$: a           -> maxBV f `max` maxBV a
  Z                 -> 0
  S e               -> maxBV e
  Rec zero step arg -> maxBV zero `max` maxBV step `max` maxBV arg

-- * Typechecker

data Mismatch
  = Mismatch String Type Type
    deriving (Show)

type Context
  = Map Name Type

typecheck' :: Syntax -> Type
typecheck' = ty Map.empty

die = error . show
mismatch s l r = die (Mismatch s l r)

ty context =
  let resolv = resolve context
      next = ty context
      inext n t = ty (intro context n t) in \case
  Z ->
    Nat
  S t ->
    let got = next t in
    if got == Nat then Nat else mismatch "S" got Nat
  Var n ->
    resolv n
  Rec zero step arg ->
    let argT = next arg
        zeroT = next zero
        stepT = next step
        prevT :--> (recT :--> newT) = stepT
    in if recT /= zeroT then mismatch "iter-rec-zero" recT zeroT else
         if prevT /= Nat then mismatch "rec-prev" prevT Nat else
           if argT /= Nat then mismatch "iter-arg" argT Nat else
             if zeroT /= newT then mismatch "iter-zero-new" zeroT newT else
               newT
  Lam n t s ->
    let left = t
        right = inext n t s
    in left :--> right
  f :$: x ->
    let dom :--> cod = next f
        gotDom = next x
    in if dom /= gotDom then mismatch "ap-dom" dom gotDom else cod

resolve :: Context -> Name -> Type
resolve context n =
  maybe (error "context fail") id (Map.lookup n context)

intro :: Context -> Name -> Type -> Context
intro c n t = Map.insert n t c

-- * Substitution

sub :: Name -> Syntax -> Syntax -> Syntax
sub n arg s = let go = sub n arg in case s of
  Var n'
    | n' == n   -> arg
    | otherwise -> Var n'
  Lam n' t b ->
    Lam n' t (go b)
  f :$: a ->
    (go f) :$: (go a)
  Z ->
    Z
  S k ->
    S (go k)
  Rec zero step arg' ->
    Rec (go zero) (go step) (go arg')

-- * Naive recursive eval

eval = \case
  Z ->
    Z
  S e ->
    S (eval e)
  Var k ->
    Var k
  lam@(Lam _ _ _) :$: a ->
    eval (apsub lam a)
  x :$: a ->
    eval (eval x :$: a)
  Rec zero _step Z ->
    eval zero
  Rec zero step (S k) ->
    -- iterator:
    --   iter 0 u v → u
    --   iter (S t) u v → v(iter t u v)
    -- recursor:
    --   0 u v → u
    --   R (S t) u v → v (R t u v) t
    eval (apsub (apsub step k) (eval (Rec zero step k)))
  Rec z s a ->
    eval (Rec z s (eval a))
  lam@(Lam _ _ _) ->
    lam
  where
    apsub (Lam n _ e) a = sub n a e
    apsub f a = apsub (eval f) a

-- * PFPL Dynamics-inspired eval

data Eval
  = Step Syntax
  | Value
    deriving Show

op = \case
  Z ->
    Value
  S e ->
    case op e of
      Value -> Value
      Step e' -> Step (S e')
  Lam _ _ _ ->
    Value
  f :$: a ->
    case op f of
      Step f' -> op (f' :$: a)
      Value ->
        case op a of
          Step a' -> op (f :$: a')
          Value ->
            case f of
              Lam n _ e -> Step (sub n a e)
              _ -> error "stuck (ap)"
  Rec zero step arg ->
    case op arg of
      Step arg' -> Step (Rec zero step arg')
      Value ->
        case op step of
          Step step' -> Step (Rec zero step' arg)
          Value ->
            case step of
              Lam npred _ (Lam nres _ b) ->
                case arg of
                  Z ->
                    Step zero
                  S nat ->
                    Step (sub nres (Rec zero step nat) (sub npred nat b))
                  _  -> error "stuck (rec)"
              _ -> error $ "op rec-step: am i supposed to break down here? " ++ show step
  _ -> error "stuck"

run e =
  case op e of
    Value -> e
    Step s -> run s
