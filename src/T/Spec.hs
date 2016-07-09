{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | Godel's System T

module T.Spec where

import Prelude hiding (exp, succ)
import Text.Show.Pretty (ppShow)

data Type
  = Nat
  | Type :--> Type
    deriving (Show, Eq)

infixr 2 :-->

class SystemT l where
  type Syn l = r | r -> l

  -- | Lambda calculus-style function application.
  --   Associates to the left.
  ($:) :: Syn l -> Syn l -> Syn l
  infixl 2 $:

  zero :: Syn l
  succ :: Syn l -> Syn l
  lam :: Type -> (Syn l -> Syn l) -> Syn l
  rec :: Syn l ->  (Syn l -> Syn l -> Syn l) -> Syn l -> Syn l

  typecheck :: Syn l -> Type
  beta :: Syn l -> Syn l

  lamn :: (Syn l -> Syn l) -> Syn l
  lamn = lam Nat

  iter :: Syn l -> (Syn l -> Syn l) -> Syn l -> Syn l
  iter zero step arg = rec zero (\_prev -> step) arg

  natlam2 :: (Syn l -> Syn l -> Syn l) -> Syn l
  natlam2 f = lamn $ \a -> lamn $ \b -> f a b

  unnat :: Syn l -> Int
  nat :: Int -> Syn l

-- * T Programs

type T l s = ( SystemT l, s ~ Syn l, Show s)

appapp :: T l s => s
appapp =
   (lam (Nat :--> Nat) (\x -> x) $: smthlam) $: zero

smthlam :: T l s => s
smthlam =
 lamn $ \x -> succ (succ (succ x))

smth :: T l s => s
smth =
  smthlam $: zero

smth2 :: T l s => s
smth2 =
  (lamn (\x -> succ (succ (succ (ap x))))) $: zero
  where
    ap x = (lamn $ \_ -> x) $: x

smth3 :: T l s => s
smth3 = (lamn (\x -> (lamn $ \_ -> x))) $: zero

smth4 :: T l s => s
smth4 = lamn $ \_ -> smth3

rcount :: T l s => s
rcount =
  lamn $ \n -> iter zero (\res -> res) n

double :: T l s => s
double =
  lamn $ \n ->
    iter zero (\res -> succ (succ res)) n

plus :: T l s => s
plus =
  lamn $ \x ->
    lamn $ \y ->
       iter
       x
       succ
       y

mult :: T l s => s
mult =
  lamn $ \x ->
    lamn $ \y ->
       iter
       zero
       (\res ->
         iter res succ y)
       x

mult' :: T l s => s
mult' =
  lamn $ \x ->
    lamn $ \y ->
       iter
       zero
       (\r -> plus $: y $: r)
       x

exp :: T l s => s
exp =
  natlam2 $ \base pow ->
    rec (succ zero) (\_prev res -> ((mult $: base) $: res)) pow

fact :: T l s => s
fact =
  lamn $ \n ->
    rec (succ zero) (\prev r -> (mult $: (succ prev)) $: r) n

-- * Test helpers

suite :: T l s => [(String, s)]
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

cute :: T l s => s -> String
cute exp = case typecheck exp of
    Nat -> show (unnat (beta exp))
    _   -> show (beta exp)

test :: T l s => [(String, s)] -> IO ()
test = mapM_ pprint . map (\(tag, e) -> (tag, e, cute e))

tytest :: T l s => [(String, s)] -> IO ()
tytest =
  mapM_ pprint . map (\(tag, e) -> (tag, e, typecheck e))

pprint :: Show a => a -> IO ()
pprint a = do
  (putStrLn . ppShow) a
  putStrLn ""
