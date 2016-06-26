{-# LANGUAGE StandaloneDeriving #-}

module Godel.Recursion where

--import Control.Arrow

newtype Fix f = In { out :: f (Fix f) }

type Algebra f a = f a -> a
type Coalgebra f a = a -> f a

-- catamorphism (fold)
cata :: Functor f => Algebra f a -> Fix f -> a
cata alg = alg . fmap (cata alg) . out

-- anamorphism (unfold)
ana :: Functor f => Coalgebra f a -> a -> Fix f
ana coalg = In . fmap (ana coalg) . coalg

--para :: Functor f => Algebra f a -> Fix f -> a
--para :: Functor f => t -> (t -> f b -> (b, t)) -> Fix f -> b
--para s alg (In f) = alg s (fmap (para s alg) f)

para :: Functor f => (f (Fix f, b) -> b) -> Fix f -> b
--para psi = snd . cata (\ fxt -> (In (fmap fst fxt), psi fxt))

para alg (In f) = alg (fmap keepCopy   f) where
  keepCopy x = (x, para alg x)


--para  c n (x : xs) = c x xs (para c n xs)
--foldr c n (x : xs) = c x    (foldr c n xs)
