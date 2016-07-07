{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -fno-warn-type-defaults
                -fno-warn-missing-signatures
                -fno-warn-unused-do-bind
                -fno-warn-unused-imports
                -fno-warn-name-shadowing #-}

-- | Godel's T: a total language with natural numbers (functorial impl)

module TF where

import Prelude hiding (exp, maxBound, succ)
import Text.Show.Pretty (ppShow)

import Godel.Recursion
import Godel.Typecheck
import Godel.Eval

-- * Syntax

type Name = Int

data SyntaxF a
  = Var Name
  | Lam Name Type a
  | App a a
  | Z
  | S a
  | Rec a Name Name a a -- ^ Rec zero x y step arg
  deriving (Show, Eq, Functor)

type Syntax = Fix SyntaxF

-- | Lambda calculus-style function application.
--   Associates to the left.
f $: a = Fix (App f a)
infixl 2 $:

maxBound :: SyntaxF Int -> Int
maxBound = \case
  Var _              -> 0
  Lam n _ _          -> n
  App f a            -> f `max` a
  Z                  -> 0
  S e                -> e
  Rec zero x _ _ arg -> zero `max` x `max` arg -- x is higher than y/body

maxBV = cata maxBound

lam :: Type -> (Syntax -> Syntax) -> Syntax
lam t f = Fix (Lam name t body)
  where
    name = maxBV body + 1
    body = f (Fix (Var name))

natlam2 :: (Syntax -> Syntax -> Syntax) -> Syntax
natlam2 f = lamn $ \a -> lamn $ \b -> f a b

lamn = lam Nat
succ = Fix . S
zero = Fix Z

rec :: Syntax ->  (Syntax -> Syntax -> Syntax) -> Syntax -> Syntax
rec zero step arg = Fix (Rec zero x y body arg)
  where
    maxBody = maxBV body
    (x, y) = (maxBody + 2, maxBody + 1)
    body = step (Fix (Var x)) (Fix (Var y))

iter :: Syntax -> (Syntax -> Syntax) -> Syntax -> Syntax
iter zero step arg = rec zero (\_prev -> step) arg

-- * Typechecker

data Type
  = Nat
  | Type :--> Type
    deriving (Show, Eq)

infixr 2 :-->

type Ctx = Context Name Type

typecheck :: Syntax -> Type
typecheck = hata' ty emptyContext

-- | Algebra for a typechecking step.
ty :: Ctx -> SyntaxF Type -> (Ctx, Type)
ty context = (\(f, t) -> (f context, t)) . \case
  Var n                 -> (id,                         resolve context n)
  Z                     -> (id,                         Nat)
  S t                   -> (id,                         match "S" t Nat t)
  Rec zero x y step arg -> (intro x Nat . intro y zero, match "rec-arg" arg Nat step)
  Lam n t s             -> (intro n t,                  t :--> s)
  App f argdom          -> let fdom :--> codom = f in
                           (id,                         match "ap-domain" fdom argdom codom)
  -- XXX: the following pattern triggers a loop. Why?
  -- App (fdomain :--> codomain) argdomain -> (id, match "ap-domain" fdomain argdomain codomain)

-- * Substitution

sub :: Name -> Syntax -> Syntax -> Syntax
sub name to = cata (sub' name to)

sub' :: Name -> Syntax -> SyntaxF Syntax -> Syntax
sub' n to = \case
  Var n'
    | n' == n   -> to
    | otherwise -> Fix (Var n')
  x             -> Fix x

-- * Small-step eval

-- | Perform a single small evaluation step.
step :: Syntax -> Eval Syntax
step = para step1

-- | Algebra for a small-step paramorphism.
--   The left part of the functor value is a "thunk".
--   This algebra matches over exactly 10 rules, ordered just like in the book!
step1 :: SyntaxF (Syntax, Eval Syntax) -> Eval Syntax
step1 = \case
  Z                                              -> Value (Fix Z)
  S (h, (Value x))                               -> Value (Fix (S h))
  Lam n t (h, e)                                 -> Value (Fix (Lam n t h))
  S (_, (Step x))                                -> Step (Fix (S x))
  App (_, Step s)                  (h, _)        -> Step (Fix (App s h))
  App (_, Value (Fix (Lam n t e))) (_, Step a)   -> Step (Fix (App (Fix (Lam n t e)) a))
  App (_, Value (Fix (Lam n _ e))) (_, Value a)  -> Step (sub n a e)
  Rec (zh, _) x y (sh, _) (_, Step nat)          -> Step (Fix (Rec zh x y sh nat))
  Rec (zh, _) _ _ _       (_, Value (Fix Z))     -> Step zh
  Rec (zh, _) x y (sh, _) (_, Value (Fix (S e))) -> Step (sub y (Fix (Rec zh x y sh e)) (sub x e sh))

-- | Perform one eval step, useful in ghci.
ds :: Syntax -> Syntax
ds = meh . step where
  meh = \case
    Value a -> a
    Step a -> a

-- * Examples

appapp =
  (lam (Nat :--> Nat) (\x -> x) $: smthlam) $: zero

smthlam =
  lam (Nat) (\x -> succ (succ (succ x)))

smth =
  smthlam $: zero

smth2 =
  (lam (Nat) (\x -> succ (succ (succ (ap x))))) $: zero
  where
    ap x = (lam (Nat) $ \_ -> x) $: x

smth3 = (lam (Nat) (\x -> (lamn $ \_ -> x))) $: zero

smth4 = lam (Nat) $ \_ -> smth3

rcount =
  lamn $ \n -> iter zero (\res -> res) n

double =
  lamn $ \n ->
    iter zero (\res -> succ (succ res)) n

plus =
  lamn $ \x ->
    lamn $ \y ->
       iter
       x
       succ
       y

mult =
  lamn $ \x ->
    lamn $ \y ->
       iter
       zero
       (\res ->
         iter res succ y)
       x

mult' =
  lamn $ \x ->
    lamn $ \y ->
       iter
       zero
       (\r -> plus $: y $: r)
       x

exp =
  natlam2 $ \base pow ->
    rec (succ zero) (\_prev res -> ((mult $: base) $: res)) pow

fact =
  lamn $ \n ->
    rec (succ zero) (\prev r -> (mult $: (succ prev)) $: r) n

-- * Test helpers

unnat = \case
  (Fix (S n)) -> 1 + unnat n
  Fix Z       -> 0
  e           -> error $ "unnat: can't eval: " ++ show e

nat = \case
  0 -> zero
  k -> succ (nat (k-1))

suite = [ ("mult", mult)
        , ("appapp", appapp)
        , ("smth", smth)
        , ("smth2", smth2)
        , ("smth3", smth3)
        , ("double 3", double $: nat 3)
        , ("2+4", (plus $: nat 2) $: nat 4)
        , ("fact 4", fact $: nat 4)
        , ("2^4", (exp $: nat 2) $: nat 4)
        , ("2*4", (mult $: nat 2) $: nat 4)
        , ("2*'4", (mult' $: nat 2) $: nat 4)
        ]

test = let
  cute exp = case typecheck exp of
      Nat -> show (unnat (run step exp))
      _ -> show (run step exp)
  evalv (tag, e) = (tag, e, cute e)
  in mapM_ (pprint . evalv) suite

tytest =
  let ty (tag, e) = (tag, e, (typecheck e)) in
  mapM_ (pprint . ty) suite

pprint :: Show a => a -> IO ()
pprint a = do
  (putStrLn . ppShow) a
  putStrLn ""
