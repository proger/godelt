{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Godel.Recursion where

newtype Fix f = Fix (f (Fix f))

deriving instance Show (f (Fix f)) => Show (Fix f)

type Algebra f a = f a -> a
type Coalgebra f a = a -> f a

-- | catamorphism (fold)
cata :: Functor f => Algebra f a -> Fix f -> a
cata alg = go where
  go (Fix t) = alg (fmap go t)

-- | anamorphism (unfold)
ana :: Functor f => Coalgebra f a -> a -> Fix f
ana coalg = go where
  go base = Fix (fmap go (coalg base))

-- | paramorphism (cata + access to previous values)
para :: Functor f => (f (Fix f, b) -> b) -> Fix f -> b
para alg = go where
  go (Fix t) = alg (fmap go' t)
  go' t = (t, go t)

-- | hylomorphism (cata + ana)
--
-- > hylo f g = f . fmap (hylo f g) . g
-- >   cata f = hylo f   unFix
-- >    ana g = hylo Fix g
--
hylo :: Functor f => Algebra f a -> Coalgebra f b -> (b -> a)
hylo f g = cata f . ana g

-- * Annotations

-- | Annotate (f r) with attribute a.
newtype AnnF f a r
  = AnnF (f r, a)
    deriving (Functor, Show, Foldable)

-- | Annotated fixed-point type. A cofree comonad.
type Ann f a
  = Fix (AnnF f a)

-- | Attribute of the root node
attr :: Ann f a -> a
attr (Fix (AnnF (_, a))) = a

-- | Bottom-up annotation.
synthesize :: forall f a. Functor f => Algebra f a -> Fix f -> Ann f a
synthesize annotationAlg = cata alg where
  alg :: Algebra f (Ann f a)
  alg fa = Fix (AnnF (fa, annotationAlg (fmap attr fa)))

-- | Annotate subtrees with sizes of children (leaves get 1).
sizes :: (Functor f, Foldable f) => Fix f -> Ann f Int
sizes = synthesize (\(t :: f Int) -> 1 + sum t)

-- | top-down, use para
inherit :: forall f a. Functor f => (Fix f -> a -> a) -> a -> Fix f -> Ann f a
inherit alg root = go root where
    go :: a -> Fix f -> Ann f a
    go p s@(Fix t) =
      let
        a = alg s p
      in Fix (AnnF ((fmap (go a) t), a))

-- | Annotate subtrees with levels to parent (root gets 1).
depths :: Functor f => Fix f -> Ann f Int
depths = inherit (\_ i -> i+1) 0

-- | Example
--
-- > data T a = Leaf String
-- >          | Node a a
-- >            deriving (Show, Functor, Foldable)
-- >
-- > tt = Fix (Node (Fix (Node (Fix $ Leaf "a") (Fix $ Leaf "b")))
-- >                (Fix (Node (Fix $ Leaf "c") (Fix $ Leaf "d"))))
--
-- > depths tt
-- > sizes tt
