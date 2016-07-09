{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

-- | System F of Polymorphic Types

module F where

import Prelude hiding (lookup)
import Text.PrettyPrint.ANSI.Leijen

import Godel.Eval
import Godel.Recursion
import Godel.Typecheck

newtype TyVar = TyVar Int deriving (Show, Ord, Eq, Enum)

data TypeF a
  = TArr a a          -- ^ Function (arrow type)
  | TVar TyVar        -- ^ Variable
  | Forall TyVar a    -- ^ Polymorphic
    deriving (Show, Functor, Eq)

type Type = Fix TypeF

newtype ExVar = ExVar Int deriving (Show, Ord, Eq, Enum)

data ExpF a
  = Var ExVar
  | Lam ExVar Type a
  | Ap a a
  | TyLam TyVar a     -- ^ Type abstraction, defines a generic type variable within 'a'.
  | TyApp Type a      -- ^ Type application, applies a polymorphic 'a' to a specific type.
    deriving (Show, Functor, Eq)

type Exp = Fix ExpF

-- Pretty printer

instance {-# OVERLAPS #-} Show Exp where show = show  . pretty
instance {-# OVERLAPS #-} Show Type where show = show  . pretty

p a = pretty a

type Prec = Rational

parensIf :: Bool -> Doc -> Doc
parensIf pred = if pred then nest 2 . parens else id

arrowLeftPrec, arrowRightPrec, arrowPrec, lamPrec,
  appPrec, appLeftPrec, appRightPrec, topPrec :: Prec
arrowLeftPrec  = 5
arrowRightPrec = 4.9
arrowPrec      = 5
lamPrec        = 1
appPrec        = 9
appLeftPrec    = 8.9
appRightPrec   = 9
topPrec        = 0

instance Pretty Type where pretty = prettyPrec topPrec
instance Pretty Exp where pretty = prettyPrec topPrec
instance Pretty ExVar where pretty (ExVar n) = char '$' <> int n
instance Pretty TyVar where pretty (TyVar n) = char '%' <> int n

class Pretty exp => PrettyPrec exp where
  prettyPrec :: Prec -> exp -> Doc

instance PrettyPrec Type where
  prettyPrec prec (Fix f) = case f of
    TVar var -> pretty var
    TArr l r ->
      parensIf (prec >= arrowPrec) $
        hsep [ prettyPrec arrowLeftPrec l
             , text "-->"
             , prettyPrec arrowRightPrec r
             ]
    Forall var body ->
      char '∀' <> parens (pretty var <> char '.' <> prettyPrec prec body)

instance PrettyPrec Exp where
  prettyPrec prec (Fix f) = case f of
    Var var -> pretty var
    Lam var ty body ->
      parensIf (prec >= lamPrec) $
        vsep [ char 'λ' <> parens (pretty var <> text ":" <+> pretty ty)
             , nest 2 $ parens (prettyPrec topPrec body)
             ]
    Ap e1 e2 ->
      parensIf (prec >= appPrec) $
        vsep [ prettyPrec appLeftPrec e1
             , prettyPrec appRightPrec e2
             ]
    TyLam var body ->
      vsep [ char 'Λ' <> parens (pretty var)
           , nest 2 $ parens (prettyPrec topPrec body)
           ]
    TyApp t body ->
      parensIf (prec >= lamPrec) $
        prettyPrec topPrec body <> char '[' <> prettyPrec topPrec t <> char ']'

-- * Type Formation checker

ok (Just x) = True
ok Nothing  = False

typeform :: Type -> Maybe Type
typeform = hata' tf emptyContext

tf :: Context TyVar Type -> TypeF (Maybe Type) -> (Context TyVar Type, Maybe Type)
tf context = refresh context . \case
  TVar tv      -> (id, do lookup context tv
                          return (Fix (TVar tv)))
  TArr ml mr   -> (id, do l <- ml
                          r <- mr
                          return (Fix (TArr l r)))
  Forall tv mt -> (let Just t = mt in intro tv t,
                   do t <- mt
                      return (Fix (Forall tv t)))

-- * Type checker for expressions

typecheck :: Exp -> Type
typecheck = hata' ty emptyContext

tsub :: TyVar -- ^ replace this variable
     -> Type  -- ^ with that type
     -> Type  -- ^ inside such term
     -> Type
tsub var sub term = cata alg term where
  alg = \case
    TVar var' | var == var' -> sub
              | otherwise   -> Fix (TVar var')
    x                       -> Fix x

ty :: Context ExVar Type -> ExpF Type -> (Context ExVar Type, Type)
ty context = refresh context . \case
  Var n        -> (id,        resolve context n)
  Lam n t s    -> (intro n t, Fix (TArr t s))
  Ap f argdom  -> (id,        let Fix (TArr fdom codom) = f in
                              match "app-domain" fdom argdom codom)
  TyLam tvar s -> (id,        Fix (Forall tvar s))
  TyApp t s    -> (id,        let Fix (Forall tvar t') = s in
                                       tsub tvar t t')

-- * Small-step operational semantics

sub :: ExVar -> Exp -> Exp -> Exp
sub n sub term = cata alg term where
  alg = \case
    Var n' | n' == n   -> sub
           | otherwise -> Fix (Var n')
    x                  -> Fix x

etsub :: TyVar -> Type -> Exp -> Exp
etsub var sub term = cata alg term where
  alg = \case
    Lam e ty x -> Fix (Lam e (tsub var sub ty) x)
    TyApp ty x -> Fix (TyApp (tsub var sub ty) x)
    x -> Fix x

step :: Exp -> Eval1 Exp
step = para step1

step1 :: ExpF (Exp, Eval1 Exp) -> Eval1 Exp
step1 = \case
  Lam n t (Any h)                      -> Value (Fix (Lam n t h))
  TyLam tv (Any h)                     -> Value (Fix (TyLam tv h))

  Ap (Any (Fix (Lam n _ e))) (Val a)   -> Step (sub n a e)
  Ap (Steps s) (Any h)                 -> Step (Fix (Ap s h))
  Ap (Val (Fix (Lam n t e))) (Steps a) -> Step (Fix (Ap (Fix (Lam n t e)) a))

  TyApp t (Any (Fix (TyLam tv e)))     -> Step (etsub tv t e)
  TyApp t (Steps s)                    -> Step (Fix (TyApp t s))

  _ -> error "stuck! did you typecheck?"

pattern Any thunk <- (thunk, _)
pattern Val thunk <- (thunk, Value _)
pattern Steps x <- (_, Step x)


-- * Macros for types and expressions

tmaxBound :: Type -> TyVar
tmaxBound = cata alg where
  alg (TVar _)     = TyVar 0
  alg (TArr l r)   = l `max` r
  alg (Forall n t) = n `max` t

emaxBound :: Exp -> (ExVar, TyVar)
emaxBound = cata alg where
  alg (Var _)      = (ExVar 0, TyVar 0)
  alg (Lam n tt e) = (n `max` fst e, tmaxBound tt `max` snd e)
  alg (Ap f a)     = (fst f `max` fst a, snd f `max` snd a)
  alg (TyLam tv e) = (fst e, snd e `max` tv)
  alg (TyApp tt e) = (fst e, snd e `max` tmaxBound tt) -- TODO: compose recursions?

-- | forall type
for'all :: (Type -> Type) -> Type
for'all f = Fix (Forall var body)
  where var = succ (tmaxBound body)
        body = f (Fix (TVar var))

-- | arrow type
(-->) :: Type -> Type -> Type
l --> r = Fix (TArr l r)
infixr 2 -->

-- | type abstraction
eΛ :: (Type -> Exp) -> Exp
eΛ f = Fix (TyLam var body)
  where var = succ (snd (emaxBound body))
        body = f (Fix (TVar var))

-- | lambda abstraction
eλ :: Type -> (Exp -> Exp) -> Exp
eλ ty f = Fix (Lam var ty body)
  where var = succ (fst (emaxBound body))
        body = f (Fix (Var var))

-- | function application (left-associative!)
(.:) :: Exp -> Exp -> Exp
f .: a = Fix (Ap f a)
infixl 2 .:

-- | type application
(%::) :: Exp -> Type -> Exp
e %:: t = Fix (TyApp t e)

-- | polymorphic function of one argument
poly1 :: (Type -> Exp -> Exp) -> Exp
poly1 f = eΛ (\t -> eλ t (\e -> f t e))

-- | polymorphic function of two arguments
poly2 :: (Type -> Exp -> Type -> Exp -> Exp) -> Exp
poly2 f = poly1 (\t1 e1 -> poly1 (\t2 e2 -> f t1 e1 t2 e2))

-- * Programs

-- * Products

-- | nullary product / unit type
t'unit = for'all (\t -> t --> t)

-- | unit value / nullary product (also polymorphic identity)
-- >>> t'unit == typecheck e'unit
-- True
e'unit = eΛ (\t -> eλ t (\x -> x))

-- | binary product constructor
e'prod :: Exp
e'prod = poly2 (\t1 e1 t2 e2 -> eΛ (\r -> eλ (t1 --> t2 --> r) (\x -> x .: e1 .: e2)))

-- | left binary product projection (fst)
e'left = undefined

-- | right binary product projection (snd)
e'right = undefined

-- * Sums

-- | nullary sum / void type
t'void = for'all (\t -> t)

-- | binary sum constructor
e'sum :: Exp
e'sum = undefined

-- * Natural numbers

t'nat :: Type
t'nat = for'all (\t -> t --> (t --> t) --> t)

-- |
-- >>> typecheck e'zero == t'nat
-- True
e'zero :: Exp
e'zero = poly1 (\t z -> eλ (t --> t) (\s -> z))

e'succ' :: Exp -> Exp
e'succ' e = poly1 (\t z -> eλ (t --> t) (\s -> s .: ((e %:: t) .: z .: s)))

e'succ :: Exp
e'succ = eλ t'nat (\pred -> poly1 (\t z -> eλ (t --> t) (\s -> s .: ((pred %:: t) .: z .: s))))

t'iter :: Type
t'iter = for'all (\t -> t --> (t --> t) --> t'nat --> t)

-- | iterator over polymorphically-encoded nats
-- >>> typecheck e'iter == t'iter
-- True
e'iter :: Exp
e'iter = poly1 (\t zero -> eλ (t --> t) (\step -> eλ t'nat (\nat -> (nat %:: t) .: zero .: step)))

e'const :: Exp
e'const = eλ t'nat (\nat -> e'succ .: e'zero)

-- | basic iteration example
-- >>> typecheck e'count == t'nat
-- True
e'count :: Exp
e'count = (e'iter %:: t'nat) .: e'zero .: e'const .: (nat 3)

nat = \case
  0 -> e'zero
  k -> e'succ .: (nat (k-1))

-- * Lists

e'list :: Exp
e'list = undefined

-- * Existentials

e'exists :: Exp
e'exists = undefined

t = run step e'count
