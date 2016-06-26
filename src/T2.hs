{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -fno-warn-type-defaults
                -fno-warn-missing-signatures
                -fno-warn-unused-do-bind
                -fno-warn-unused-imports
                -fno-warn-name-shadowing #-}

module T2 where

import Prelude hiding (exp, succ)
import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace
import Text.PrettyPrint (Doc, (<+>), (<>))
import qualified Text.PrettyPrint as P

import Godel.Recursion

type Name = Int

data Type
  = Nat
  | Type :-> Type
    deriving (Show, Eq)

data Syntax a
  = Var Name
  | Z
  | S a
  | Lam Name Type a
  | a :$: a
  | Rec a a a
    deriving (Show, Eq, Functor)

type AST = Fix Syntax

maxBV :: Algebra Syntax Int
maxBV = \case
  Var _     -> 0 -- important: mustn't look at this constructor!
  Z         -> 0
  S a       -> a
  Lam n _ _ -> n
  f :$: a   -> f `max` a
  Rec z s a -> z `max` s `max` a

doc :: Algebra Syntax Doc
doc = let var n = P.text "x" <> P.int n in \case
  Var n     -> var n
  Z         -> P.text "Z"
  S a       -> P.text "S" <+> P.parens a
  Lam n t a -> P.parens (P.text "\\" <> var n <> P.text (":" ++ show t) <> (P.text "." <+> a))
  f :$: a   -> P.brackets f <> P.parens a
  Rec z s a -> P.text "rec" <+> z <+> P.braces s <+> P.braces a

pprint :: AST -> Doc
pprint = cata doc

-- * sugar (syntax api)

lam :: Type -> (AST -> AST) -> AST
lam t f = In (Lam fresh t body)
  where
    body = f (In (Var fresh))
    fresh = cata maxBV body + 1

nat :: Int -> AST
nat n | n <= 0    = In Z
      | otherwise = In (S (nat (n-1)))

zero = nat 0
succ a = In (S a)

rec :: AST -> AST -> AST -> AST
rec z s a = In (Rec z s a)

iter :: AST -> AST -> AST -> AST
iter z s a = rec z (lam Nat $ \_prev -> s) a

reclam :: Type -> AST -> (AST -> AST -> AST) -> AST -> AST
reclam t z f a = rec z (lam Nat $ \prev -> lam t (f prev)) a

-- * typechecker

type Context = Map Name Type

ty :: Syntax (Fix Syntax, (Context, Type)) -> (Context, Type)
ty thing =
  let
    --resolve = maybe (error "context fail") id . flip Map.lookup context
    resolve = undefined
    keep t = undefined
    --extend  = ty
  in case undefined of
    Var n     -> resolve n
    Z         -> keep Nat
    S a       -> if a == Nat then keep Nat else error "succ"
    --Lam n t a ->
    -- Lam n t a -> P.parens (P.text "\\" <> var n <> P.text (":" ++ show t) <> (P.text "." <+> a))
    -- f :$: a   -> P.brackets f <> P.parens a
    -- Rec z s a -> P.text "rec" <+> z <+> P.braces s <+> P.braces a

--typecheck :: AST -> Type
typecheck :: AST -> Type
typecheck = snd . para ty

-- * syntax

plus =
  lam Nat $ \x ->
    lam Nat $ \y ->
      iter x (lam Nat $ \r -> succ r) y

t1, t2, t3, t4 :: AST

t1 = In (Var 1)
t2 = nat 3
t3 = lam Nat (\_ -> nat 4)
t4 = In (S (In Z))
