{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-type-defaults
                -fno-warn-missing-signatures
                -fno-warn-unused-do-bind
                -fno-warn-unused-imports
                -fno-warn-name-shadowing #-}

-- | Godel's T: a total language with natural numbers

module T1 where

import Prelude hiding (exp)
import Text.Show.Pretty (ppShow)
import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace

import Godel.Eval

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

lam :: Type -> (Syntax -> Syntax) -> Syntax
lam t f = Lam name t body
  where
    name = maxBV body + 1
    body = f (Var name)

-- * Typechecker

data Type
  = Nat
  | Type :--> Type
    deriving (Show, Eq)

infixr 2 :-->

data Mismatch
  = Mismatch String Type Type
    deriving (Show)

type Context
  = Map Name Type

typecheck :: Syntax -> Type
typecheck = ty Map.empty

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

ts m a = traceShow (m, a) a

sub :: Name -> Syntax -> Syntax -> Syntax
sub n arg s = let go = sub n arg in case s of
  Var n'
    | n' == n        -> arg
    | otherwise      -> Var n'
  Lam n' t b         -> Lam n' t (go b)
  f :$: a            -> (go f) :$: (go a)
  Z                  -> Z
  S k                -> S (go k)
  Rec zero step arg' -> Rec (go zero) (go step) (go arg')

-- * Small-step operational semantics

op :: Syntax -> Eval Syntax
op = \case
  Z                                     -> Value Z
  S e                                   -> S <$> op e
  lam@(Lam _ _ _)                       -> Value lam
  f@(Lam n _ e) :$: a                   -> eval (op . (f :$:)) (const (Step (sub n a e))) (op a)
  f :$: a                               -> fmap (:$: a) (op f)
  Rec z _ Z                             -> Step z
  Rec z st@(Lam p _ (Lam r _ b)) (S pn) -> Step (sub r (Rec z st pn) (sub p pn b))
  Rec z st@(Lam _ _ (Lam _ _ _)) nat    -> fmap (\nat' -> Rec z st nat') (op nat)
  Rec z st nat                          -> fmap (\st' -> Rec z st' nat) (op st)
  _                                     -> error "stuck"

-- * Sugar

iter :: Syntax -> Syntax -> Syntax -> Syntax
iter zero step arg =
  Rec zero (lam Nat $ \_prev -> step) arg

natlam2 :: (Syntax -> Syntax -> Syntax) -> Syntax
natlam2 f = lam Nat $ \a -> lam Nat $ \b -> f a b

lamn = lam Nat

natrec :: Syntax -> (Syntax -> Syntax -> Syntax) -> Syntax -> Syntax
natrec zero step arg =
  Rec zero (lam Nat $ \prev ->
             lam Nat $ \res ->
              step prev res) arg

-- * Examples

appapp =
  (lam (Nat :--> Nat) (\x -> x) :$: smthlam) :$: Z

smthlam =
  (lam (Nat) (\x -> S (S (S x))))

smth = smthlam :$: Z

smth2 =
  (lam (Nat) (\x -> S (S (S (ap x))))) :$: Z
  where
    ap x = (lam (Nat) $ \_ -> x) :$: x

smth3 = (lam (Nat) (\x -> (lam Nat $ \_ -> x))) :$: Z

smth4 = lam (Nat) $ \_ -> smth3

rcount =
  lam Nat $ \n -> iter Z (lam Nat $ \res -> res) n

double =
  lam Nat $ \n ->
    iter Z (lam Nat $ \res -> S (S res)) n

plus =
  lam Nat $ \x ->
    lam Nat $ \y ->
       iter
       x
       (lam Nat S)
       y

mult =
  lam Nat $ \x ->
    lam Nat $ \y ->
       iter
       Z
       (lam Nat $ \res ->
         iter res (lam Nat S) y)
       x

mult' =
  lam Nat $ \x ->
    lam Nat $ \y ->
       iter
       Z
       (plus :$: y)
       x

exp =
  natlam2 $ \base pow ->
    natrec (S Z) (\_prev res -> ((mult :$: base) :$: res)) pow

fact =
  lam Nat $ \n ->
    natrec (S Z) (\prev r -> (mult :$: (S prev)) :$: r) n

-- * Test helpers

unnat = \case
  S n -> 1 + unnat n
  Z -> 0
  e -> error $ "unnat: can't eval: " ++ show e

nat = \case
  0 -> Z
  k -> S (nat (k-1))

suite = [ ("mult", mult)
        , ("smth", smth)
        , ("smth2", smth2)
        , ("smth3", smth3)
        , ("double 3", double :$: nat 3)
        , ("2+4", (plus :$: nat 2) :$: nat 4)
        , ("fact 4", fact :$: nat 4)
        , ("2^4", (exp :$: nat 2) :$: nat 4)
        , ("2*4", (mult :$: nat 2) :$: nat 4)
          -- this one will fail with `run`
        , ("2*'4", (mult' :$: nat 2) :$: nat 4)
        ]

test =
  -- let evalv (tag, e) = (tag, e, run e) in
  let evalv (tag, e) = (tag, e, run op e) in
  mapM_ (pprint . evalv) suite

tytest =
  let ty (tag, e) = (tag, e, (typecheck e)) in
  mapM_ (pprint . ty) suite

pprint :: Show a => a -> IO ()
pprint a = do
  (putStrLn . ppShow) a
  putStrLn ""
