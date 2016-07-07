{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE InstanceSigs #-}

{-# OPTIONS_GHC -fno-warn-type-defaults
                -fno-warn-missing-signatures
                -fno-warn-unused-do-bind
                -fno-warn-unused-imports
                -fno-warn-name-shadowing #-}

-- | Godel's T: a total language with natural numbers (functorial impl)

module TF where

import Prelude hiding (succ, maxBound)
import Godel.Recursion
import Godel.Typecheck
import Godel.Eval

import Spec.T

data TF

instance SystemT TF where
   type Syn TF = Fix SyntaxF

   typecheck = typecheck'
   beta = run step

   f $: a = Fix (App f a)

   zero = Fix Z
   succ = Fix . S

   lam :: Type -> (Syntax -> Syntax) -> Syntax
   lam t f = Fix (Lam name t body)
     where
       name = maxBV body + 1
       body = f (Fix (Var name))

   lamn :: (Syntax -> Syntax) -> Syntax
   lamn = lam Nat

   rec :: Syntax -> (Syntax -> Syntax -> Syntax) -> Syntax -> Syntax
   rec zero step arg = Fix (Rec zero x y body arg)
     where
       maxBody = maxBV body
       (x, y) = (maxBody + 2, maxBody + 1)
       body = step (Fix (Var x)) (Fix (Var y))

   unnat = \case
     (Fix (S n)) -> 1 + unnat n
     Fix Z       -> 0
     e           -> error $ "unnat: can't eval: " ++ show e

   nat = \case
     0 -> zero
     k -> succ (nat (k-1))

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

maxBound :: SyntaxF Int -> Int
maxBound = \case
  Var _              -> 0
  Lam n _ _          -> n
  App f a            -> f `max` a
  Z                  -> 0
  S e                -> e
  Rec zero x _ _ arg -> zero `max` x `max` arg -- x is higher than y/body

maxBV = cata maxBound

-- * Typechecker

type Ctx = Context Name Type

typecheck' :: Syntax -> Type
typecheck' = hata' ty emptyContext

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
step :: Syntax -> Eval1 Syntax
step = para step1

-- | Algebra for a small-step paramorphism.
--   The left part of the functor value is a "thunk".
--   This algebra matches over exactly 10 rules, ordered just like in the book!
step1 :: SyntaxF (Syntax, Eval1 Syntax) -> Eval1 Syntax
step1 = \case
  Z                                         -> Value (Fix Z)
  S (Val h)                                 -> Value (Fix (S h))
  Lam n t (Val h)                           -> Value (Fix (Lam n t h))
  S (Steps x)                               -> Step (Fix (S x))
  App (Steps s) (Val h)                     -> Step (Fix (App s h))
  App (Val (Fix (Lam n t e))) (Steps a)     -> Step (Fix (App (Fix (Lam n t e)) a))
  App (Val (Fix (Lam n _ e))) (Val a)       -> Step (sub n a e)
  Rec (Val z) x y (Val s) (Steps nat)       -> Step (Fix (Rec z x y s nat))
  Rec (Val z) _ _ _       (Val (Fix Z))     -> Step z
  Rec (Val z) x y (Val s) (Val (Fix (S e))) -> Step (sub y (Fix (Rec z x y s e)) (sub x e s))

pattern Val thunk <- (thunk, Value _)
pattern Steps x <- (_, Step x)

-- -- | Perform one eval step, useful in ghci.
ds :: Syntax -> Syntax
ds = meh . step where
  meh = \case
    Value a -> a
    Step a -> a
