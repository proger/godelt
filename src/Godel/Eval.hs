{-# LANGUAGE LambdaCase #-}

-- | Functions for implementing small-step (structural) operational semantics.

module Godel.Eval where

import Godel.Recursion

data Eval v s
  = Step s
  | Value v
    deriving (Show)

instance Functor (Eval v) where
  fmap f (Step s)  = Step (f s)
  fmap _ (Value v) = Value v

-- | Almost the same as 'Data.Either.either'.
eval :: (s -> r) -> (v -> r) -> Eval v s -> r
eval step value = \case
  Step a -> step a
  Value a -> value a

run :: Coalgebra (Eval a) b -> b -> a
run = hylo drop
  where
    drop (Step k) = k
    drop (Value v) = v
