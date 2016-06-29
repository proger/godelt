-- | Plotkin's PCF: a partial language with general recursion and natural numbers

{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-type-defaults
                -fno-warn-missing-signatures
                -fno-warn-unused-do-bind
                -fno-warn-unused-imports
                -fno-warn-name-shadowing #-}

module PCF where

import Text.Show.Pretty (ppShow)
import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace

-- * Syntax

type Name = Int

data Syntax
  = Var Name
  | Lam Name Type Syntax
  | Syntax :$: Syntax
  | Z
  | S Syntax
  | Ifz Syntax Syntax Syntax
  | Fixpoint Name Type Syntax
    deriving (Show, Eq)

-- Lambda calculus-style function application associates to the left.
infixl 2 :$:

-- | Axelsson & Claessen, Using Circular Programs for Higher-Order Syntax
maxBV :: Syntax -> Int
maxBV = \case
  Var _          -> 0
  Lam n _ _      -> n
  f :$: a        -> maxBV f `max` maxBV a
  Z              -> 0
  S e            -> maxBV e
  Ifz i z s      -> maxBV i `max` maxBV z `max` maxBV s
  Fixpoint n _ _ -> n

defn :: (Name -> Type -> Syntax -> Syntax) -> Type -> (Syntax -> Syntax) -> Syntax
defn cons t f = cons name t body
  where
    name = maxBV body + 1
    body = f (Var name)

lam = defn Lam
fixpoint = defn Fixpoint

-- * Typechecker

data Type
  = Nat
  | Type :--\ Type
    deriving (Show, Eq)

data Mismatch
  = Mismatch String Type Type
    deriving (Show)

type Context
  = Map Name Type

typecheck :: Syntax -> Type
typecheck = ty Map.empty

match rule l r next =
  if l /= r
  then error (show (Mismatch rule l r))
  else next

ty context =
  let resolv = resolve context
      next = ty context
      inext n t = ty (intro context n t) in \case
  Z ->
    Nat
  S t ->
    match "S" (next t) Nat Nat
  Var n ->
    resolv n
  Ifz z s nat ->
    let natT = next nat
        zeroT = next z
        prevT :--\ newT = next s
    in match "ifz-rec-zero" zeroT newT $
       match "ifz-prev" prevT Nat $
       match "ifz-nat" natT Nat $
       match "ifz-zero-new" zeroT newT $
       newT
  Lam n t s ->
    let left = t
        right = inext n t s
    in left :--\ right
  f :$: x ->
    let dom :--\ cod = next f
    in match "ap-dom" dom (next x) cod
  Fixpoint n t s ->
    let left = t
        right = inext n t s
    in match "fixpoint" left right right

resolve :: Context -> Name -> Type
resolve context n =
  maybe (error "context fail") id (Map.lookup n context)

intro :: Context -> Name -> Type -> Context
intro c n t = Map.insert n t c

-- * substitution

ts m a = traceShow (m, a) a

-- | subfix is essentially a hack that avoids capturing `Fixpoint` during substitution
--   at the cost of renumbering everything.
subfix :: Syntax -> Syntax
subfix (Fixpoint n t b) =
  let
    bump :: (Name -> Name) -> Syntax -> Syntax
    bump f = let go = bump f in \case
      Var n' ->
        Var (f n')
      Lam n' t b ->
        Lam (f n') t (go b)
      Fixpoint n' t b ->
        Fixpoint (f n') t (go b)
      l :$: r ->
        (go l) :$: (go r)
      Z ->
        Z
      S k ->
        S (go k)
      Ifz z s nat ->
        Ifz (go z) (go s) (go nat)

    oldmax = maxBV b + 1
    b' = bump (+ oldmax) b
    fx = fixpoint t (\arg -> sub n arg b)
  in sub (n + oldmax) fx b'
subfix _ = error "stuck: subfix"

sub :: Name -> Syntax -> Syntax -> Syntax
sub n arg s = let go = sub n arg in case s of
  Var n'
    | n' == n   -> arg
    | otherwise -> Var n'
  Lam n' t b ->
    Lam n' t (go b)
  Fixpoint n' t b ->
    Fixpoint n' t (go b)
  f :$: a ->
    (go f) :$: (go a)
  Z ->
    Z
  S k ->
    S (go k)
  Ifz z s nat ->
    Ifz (go z) (go s) (go nat)

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
  Ifz zero step arg ->
    case op arg of
      Step arg' -> Step (Ifz zero step arg')
      Value ->
        case op step of
          Step step' -> Step (Ifz zero step' arg)
          Value ->
            case step of
              Lam npred _ s ->
                case arg of
                  Z ->
                    Step zero
                  S nat ->
                    Step (sub npred nat s)
                  _  -> error "stuck (rec)"
              _ -> error $ "op ifz-step: stuck"
  fx@(Fixpoint _ _ _) ->
    Step (subfix fx)
  _ -> error "stuck"

op' s = (\(Step x) -> x) (op s)

run e =
  case op e of
    Value -> e
    Step s -> run s

-- * Sugar

iter :: Syntax -> Syntax -> Syntax -> Syntax
iter zero step arg =
  fixpoint
    (Nat :--\ Nat)
    (\f -> lam Nat $ Ifz zero (lam Nat $ \npred -> step :$: (f :$: npred)))
  :$: arg

-- * Examples

-- | mult: same as in T1!
mult =
  lam Nat $ \x ->
    lam Nat $ \y ->
       iter
       Z
       (lam Nat $ \res ->
         iter res (lam Nat S) y)
       x

-- | > fact = fix (\f -> \n -> if n == 0 then 1 else n * f (n-1))
fact =
  lam Nat $ \x ->
    fixpoint
      (Nat :--\ Nat)
      (\f ->
        lam Nat (\n ->
                  Ifz
                  (S Z)
                  (lam Nat $ \npred -> mult :$: (f :$: npred) :$: n)
                  n))
    :$: x

-- * Test helpers

unnat = \case
  S n -> 1 + unnat n
  Z -> 0
  e -> error $ "unnat: can't eval: " ++ show e

nat = \case
  0 -> Z
  k -> S (nat (k-1))

suite = [ ("fact 4", fact :$: nat 4)
        , ("5 * 6", mult :$: nat 5 :$: nat 6)
        ]

test =
  let
    cute exp = case typecheck exp of
      Nat -> show (unnat (run exp))
      _ -> show (run exp)
    evalv (tag, e) = (tag, e, cute e)
  in mapM_ (pprint . evalv) suite

tytest =
  let ty (tag, e) = (tag, e, (typecheck e)) in
  mapM_ (pprint . ty) suite

pprint :: Show a => a -> IO ()
pprint a = do
  (putStrLn . ppShow) a
  putStrLn ""
