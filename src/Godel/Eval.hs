{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

-- | Functions for implementing small-step (structural) operational semantics.

module Godel.Eval where

data Eval a
  = Step a
  | Value a
    deriving (Show, Functor)

-- | Almost the same as 'Data.Either.either'.
eval :: (a -> r) -> (a -> r) -> Eval a -> r
eval step value = \case
  Step a -> step a
  Value a -> value a

run :: (a -> Eval a) -> a -> a
run step = eval (run step) id . step
