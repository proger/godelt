{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-type-defaults
                -fno-warn-missing-signatures
                -fno-warn-unused-do-bind
                -fno-warn-unused-imports
                -fno-warn-name-shadowing #-}


module Lib where

import Text.Show.Pretty (ppShow)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Exception.Base
import Data.Typeable

-- * syntax

-- | One common issue in implementing programming languages is representing names/variables/identifiers in such a way that you can check α-equivalence of syntax trees and correctly implement (capture-avoiding) substitution
data Name
  = X Int
    deriving (Eq, Ord)

x1 = X 1
x2 = X 2
x3 = X 3
x4 = X 4

instance Show Name where
  show (X i) = "x" ++ show i

fresh :: Name
fresh = undefined

equalsName :: Name -> Name -> Bool
equalsName = undefined

-- | Annotation.
data TypeAnn
  = T
    deriving (Show, Eq)

-- | A problem with this representation is that, as you traverse a term, you need to remember to substitute fresh variables at appropriate times to avoid accidental problems with α-equivalence and substitution, because the same Name might be used in many places with different meanings
data Syntax
  = Var Name
  | Lam Name Type Syntax
  | Ap Syntax Syntax
  | Z
  | S Syntax
  | Rec Syntax Syntax Syntax
  deriving (Show, Eq)

-- Axelsson & Claessen, Using Circular Programs for Higher-Order Syntax
maxBV :: Syntax -> Int
maxBV = \case
  Var _ -> 0
  Lam (X n) _ _ -> n
  Ap f a -> maxBV f `max` maxBV a
  Z -> 0
  S e -> maxBV e
  Rec zero step arg -> maxBV zero `max` maxBV step `max` maxBV arg

sub :: Name -> Syntax -> Syntax
sub = undefined

equalsSyntax :: Syntax -> Syntax -> Bool
equalsSyntax = undefined

lam :: Type -> (Syntax -> Syntax) -> Syntax
lam t f = Lam name t body
  where
    name = X (maxBV body + 1)
    body = f (Var name)

-- * typechecker

data Type
  = Nat
  | Arr Type Type
    deriving (Show, Eq)

type Context = Map Name Type

typecheck :: Syntax -> Type
typecheck = ty Map.empty

die = error . show
mismatch s l r = die (Mismatch s l r)

data Mismatch = Mismatch String Type Type deriving (Show, Typeable)

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
        Arr predT (Arr oldT newT) = stepT
    in if oldT /= zeroT then mismatch "rec-zero/res" zeroT oldT else
         if predT /= Nat then mismatch "rec-pred" predT Nat else
           if argT /= Nat then mismatch "rec-arg" argT Nat else
             if oldT /= newT then mismatch "rec-old/new" oldT newT else
               newT
  Lam n t s ->
    let left = t
        right = inext n t s
    in Arr left right
  Ap f x ->
    let Arr dom cod = next f
        gotDom = next x
    in if dom /= gotDom then mismatch "ap-dom" dom gotDom else cod

resolve :: Context -> Name -> Type
resolve context n =
  maybe (error "context fail") id (Map.lookup n context)

intro :: Context -> Name -> Type -> Context
intro c n t = Map.insert n t c

-- * examples

smth =
  Ap (lam (Nat) (\x -> S (S (S x)))) Z

smth2 =
  Ap (lam (Nat) (\x -> S (S (S (ap x))))) Z
  where
    ap x = (Ap (lam (Nat) $ \y -> x) x)

smth3 = Ap (lam (Nat) (\x -> (lam (Nat) $ \y -> x))) Z

smth4 = lam (Nat) $ \x -> smth3

-- pair = lam (\x -> lam (\y -> lam (\z -> (Ap z (Ap x y)))))

-- first  = lam (\p -> Ap p (lam (\x -> lam (\y -> x))))
-- second = lam (\p -> Ap p (lam (\x -> lam (\y -> y))))

-- zzp = Ap first (Ap (Ap pair Z) Z)

double = lam Nat $ \n -> Rec Z (lam Nat $ \_pred -> lam Nat $ \res -> S (S res)) n

weird1 = Ap Z Z
weird2 = Ap (S Z) Z

test = mapM_ pprint [ smth, smth2, smth3, (\(Ap (Lam _ _ t) _) -> t) smth2, smth4]

pprint = putStrLn . ppShow
