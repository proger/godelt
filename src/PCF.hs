{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-type-defaults
                -fno-warn-missing-signatures
                -fno-warn-unused-do-bind
                -fno-warn-unused-imports
                -fno-warn-name-shadowing #-}

-- | Plotkin's PCF: a partial language with general recursion and natural numbers

module PCF where

import Prelude hiding (gcd, subtract)
import Data.Function
import Text.Show.Pretty (ppShow)
import Debug.Trace

import Godel.Eval
import Godel.Typecheck

-- * Syntax

type Name = Int

data Syntax
  = Var Name
  | Lam Name Type Syntax
  | Syntax :$: Syntax
  | Z
  | S Syntax
  | Fixpoint Name Type Syntax
  | Ifz Syntax Syntax Syntax -- ^ The third argument is not supposed to be a lambda
                             --   in the original PCF, this impl is relaxed.
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
  | Type :--\ Type -- ^ "harpoon" -- denotes partial function types
    deriving (Show, Eq)

infixr 2 :--\

-- | 'error'\'s when typechecking fails.
typecheck :: Syntax -> Type
typecheck = ty emptyContext

ty context =
  let resolv = resolve context
      next = ty context
      inext n t = ty (intro context n t)
  in \case
  Z              -> Nat
  S t            -> match "S" (next t) Nat Nat
  Var n          -> resolv n
  Lam n t s      -> let left = t; right = inext n t s in left :--\ right
  f :$: x        -> let dom :--\ cod = next f in match "ap-dom" dom (next x) cod
  Fixpoint n t s -> let left = t; right = inext n t s in match "fixpoint" left right right
  Ifz z s nat    ->
    let natT = next nat
        zeroT = next z
        prevT :--\ newT = next s
    in match "ifz-rec-zero" zeroT newT $
       match "ifz-prev" prevT Nat $
       match "ifz-nat" natT Nat $
       match "ifz-zero-new" zeroT newT $
       newT

-- * substitution

ts m a = traceShow (m, a) a

-- | subfix is essentially a hack that avoids capturing `Fixpoint` during substitution
--   at the cost of renumbering everything.
subfix :: Syntax -> Syntax
subfix (Fixpoint n t b) =
  let
    bump :: (Name -> Name) -> Syntax -> Syntax
    bump f = let go = bump f in \case
      Var n'          -> Var (f n')
      Lam n' t b      -> Lam (f n') t (go b)
      Fixpoint n' t b -> Fixpoint (f n') t (go b)
      l :$: r         -> (go l) :$: (go r)
      Z               -> Z
      S k             -> S (go k)
      Ifz z s nat     -> Ifz (go z) (go s) (go nat)

    oldmax = maxBV b + 1
    b' = bump (+ oldmax) b
    fx = fixpoint t (\arg -> sub n arg b)
  in sub (n + oldmax) fx b'
subfix _ = error "stuck: subfix"

sub :: Name -> Syntax -> Syntax -> Syntax
sub n arg s = let go = sub n arg in case s of
  Var n'
    | n' == n     -> arg
    | otherwise   -> Var n'
  Lam n' t b      -> Lam n' t (go b)
  Fixpoint n' t b -> Fixpoint n' t (go b)
  f :$: a         -> (go f) :$: (go a)
  Z               -> Z
  S k             -> S (go k)
  Ifz z s nat     -> Ifz (go z) (go s) (go nat)

-- * PFPL Dynamics-inspired eval

-- | Apply one evaluation rule.
op :: Syntax -> Eval Syntax
op = let notLam = \case Lam _ _ _ -> False; _ -> True in \case
  Z                               -> Value Z
  S e                             -> fmap S (op e)
  f@(Lam _ _ _)                   -> Value f
  f@(Lam n _ e) :$: a             -> eval (op . (f :$:)) (const (Step (sub n a e))) (op a)
  f :$: a                         -> fmap (:$: a) (op f)
  fx@(Fixpoint _ _ _)             -> Step (subfix fx)
  Ifz zero (Lam _ _ _) Z          -> Step zero
  Ifz _ (Lam npred _ s) (S nat)   -> Step (sub npred nat s)
  Ifz zero step@(Lam _ _ _) arg   -> fmap (\arg' -> Ifz zero step arg') (op arg)
  Ifz zero step arg | notLam step -> fmap (\step' -> Ifz zero step' arg) (op step)
  _                               -> error "stuck"

-- * Sugar / macros

-- | Simulates 'T1.iter'.
iter :: Syntax -> Syntax -> Syntax -> Syntax
iter zero step arg =
  fixpoint
    (Nat :--\ Nat)
    (\f -> lam Nat $ Ifz zero (lam Nat $ \npred -> step :$: (f :$: npred)))
  :$: arg

lamn :: (Syntax -> Syntax) -> Syntax
lamn = lam Nat

-- | > ifz pred then else
ifz :: Syntax -> Syntax -> (Syntax -> Syntax) -> Syntax
ifz i t e = Ifz t (lamn e) i

-- | Subtraction macro.
(/-\) :: Syntax -> Syntax -> Syntax
m /-\ n = subtract :$: m :$: n

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

-- | Greater or equal.
gte :: Syntax
gte =
  fixpoint (Nat :--\ Nat :--\ Nat)
    (\f ->
      lamn (\x ->
        lamn (\y ->
               ifz x
               (ifz y yes (const no))
               (\x' -> (ifz y yes (f :$: x' :$:))))))
  where
    yes = S Z
    no = Z

subtract :: Syntax
subtract =
  fixpoint (Nat :--\ Nat :--\ Nat)
    (\f ->
      lamn (\x ->
        lamn (\y ->
               ifz y
               (ifz x Z S)
               (\y' -> (ifz x y' (\x' -> f :$: x' :$: y'))))))

-- | Greatest common divisor.
--
-- > ggcd f m n =
-- >  if m == n then m else if m > n
-- >                        then f (m-n) n
-- >                        else f m (n-m)
gcd =
  fixpoint (Nat :--\ Nat :--\ Nat)
    (\f -> lamn (\m -> lamn (\n ->
      ifz n
      m
      (const
       (ifz m
        n
        (const
         (ifz (gte :$: m :$: n)
          ({-n >  m-} f :$: m :$: (n /-\ m))
          ({-n <= m-} const $ f :$: (m /-\ n) :$: n))))))))

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
        , ("14 - 3", nat 14 /-\ nat 3)
        , ("gcd 14 21", gcd :$: nat 14 :$: nat 21)
        ]

test =
  let
    cute exp = case typecheck exp of
      Nat -> show (unnat (run op exp))
      _ -> show (run op exp)
    evalv (tag, e) = (tag, e, cute e)
  in mapM_ (pprint . evalv) suite

tytest =
  let ty (tag, e) = (tag, e, (typecheck e)) in
  mapM_ (pprint . ty) suite

pprint :: Show a => a -> IO ()
pprint a = do
  (putStrLn . ppShow) a
  putStrLn ""
