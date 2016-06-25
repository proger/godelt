{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-type-defaults
                -fno-warn-missing-signatures
                -fno-warn-unused-do-bind
                -fno-warn-unused-imports
                -fno-warn-name-shadowing #-}

module T1 where

import Text.Show.Pretty (ppShow)
import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace

-- * syntax

-- | One common issue in implementing programming languages is representing names/variables/identifiers in such a way that you can check α-equivalence of syntax trees and correctly implement (capture-avoiding) substitution
data Name
  = X Int
    deriving (Eq, Ord)

instance Show Name where show (X i) = "x" ++ show i

x1 = X 1
x2 = X 2
x3 = X 3
x4 = X 4

-- | A problem with this representation is that, as you traverse a term, you need to remember to substitute fresh variables at appropriate times to avoid accidental problems with α-equivalence and substitution, because the same Name might be used in many places with different meanings
data Syntax
  = Var Name
  | Lam Name Type Syntax
  | Ap Syntax Syntax
  | Z
  | S Syntax
  | Iter Syntax Syntax Syntax
  deriving (Show, Eq)

-- Axelsson & Claessen, Using Circular Programs for Higher-Order Syntax
maxBV :: Syntax -> Int
maxBV = \case
  Var _ -> 0
  Lam (X n) _ _ -> n
  Ap f a -> maxBV f `max` maxBV a
  Z -> 0
  S e -> maxBV e
  Iter zero step arg -> maxBV zero `max` maxBV step `max` maxBV arg

sub :: Name -> Syntax -> Syntax -> Syntax
sub n arg s = let go = sub n arg in case s of
  Var n'
    | n' == n   -> arg
    | otherwise -> Var n'
  Lam n' t b
    -- | n' == n ->
    --   peel off a lambda
    --   go b
    | otherwise ->
      Lam n' t (go b)
  Ap f a ->
    Ap (go f) (go a)
  Z ->
    Z
  S k ->
    S (go k)
  Iter zero step arg' ->
    Iter (go zero) (go step) (go arg')

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
  Iter zero step arg ->
    let argT = next arg
        zeroT = next zero
        stepT = next step
        Arr predT newT = stepT
    in if predT /= Nat then mismatch "iter-pred" predT Nat else
         if argT /= Nat then mismatch "iter-arg" argT Nat else
           if zeroT /= newT then mismatch "iter-zero-new" zeroT newT else
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

-- * eval

ts m a = traceShow (m, a) a

eval = \case
  Z ->
    Z
  S e ->
    S (eval e)
  Var k ->
    Var k
  Ap lam@(Lam _ _ _) a ->
    eval (apsub lam a)
  Ap x a ->
    eval (Ap (eval x) a)
  Iter zero _step Z ->
    eval zero
  Iter zero step (S k) ->
    -- iterator:
    -- iter 0 u v → u
    -- iter (S t) u v → v(iter t u v)
    eval (apsub step (Iter zero step k))
  Iter z s a ->
    eval (Iter z s (eval a))
  -- recursor: (TODO)
  -- R 0 u v → u
  -- R (S t) u v → v (R t u v) t
  lam@(Lam _ _ _) ->
    lam
  where
    apsub (Lam n _ e) a = sub n a e
    apsub f a = apsub (eval f) a

-- * examples

smth =
  Ap (lam (Nat) (\x -> S (S (S x)))) Z

smth2 =
  Ap (lam (Nat) (\x -> S (S (S (ap x))))) Z
  where
    ap x = (Ap (lam (Nat) $ \_ -> x) x)

smth3 = Ap (lam (Nat) (\x -> (lam (Nat) $ \_ -> x))) Z

smth4 = lam (Nat) $ \_ -> smth3

double =
  lam Nat $ \n ->
    Iter Z (lam Nat $ \res -> S (S res)) n

plus =
  lam Nat $ \x ->
    lam Nat $ \y ->
       Iter
       x
       (lam Nat S)
       y

-- TODO: prove mult mult' are equal

mult =
  lam Nat $ \x ->
    lam Nat $ \y ->
       Iter
       Z
       (lam Nat $ \res ->
         Iter res (lam Nat S) y)
       x

mult' =
  lam Nat $ \x ->
    lam Nat $ \y ->
       Iter
       Z
       (Ap plus y)
       x

exp = undefined

-- fac: can't do it with iter! need rec.
-- fac = \case
--   lam Nat $ \n ->
--     Iter (S Z) (lam Nat \r -> Ap mult r ) n

fac = \case
  0 -> 1
  n -> n * fac (n-1)

count = \case
  S n -> 1 + count n
  Z -> 0
  e -> error $ "count: can't eval: " ++ show e

uncount = \case
  0 -> Z
  k -> S (uncount (k-1))

weird1 = Ap Z Z
weird2 = Ap (S Z) Z

-- | Church pairs: need untyped lambdas
-- pair = lam (\x -> lam (\y -> lam (\z -> (Ap z (Ap x y)))))
-- first  = lam (\p -> Ap p (lam (\x -> lam (\y -> x))))
-- second = lam (\p -> Ap p (lam (\x -> lam (\y -> y))))
-- zzp = Ap first (Ap (Ap pair Z) Z)

data Id a
  = a :===: a
    deriving Show

test =
  let evalv e = e :===: (eval e) in
  mapM_ (pprint . evalv) [ smth
                        , smth2
                        , smth3
                        , (\(Ap (Lam _ _ t) _) -> t) smth2
                        , smth4
                        , (Ap (Ap mult (uncount 2)) (uncount 4)) ]

pprint :: Show a => a -> IO ()
pprint a = do
  (putStrLn . ppShow) a
  putStrLn ""
