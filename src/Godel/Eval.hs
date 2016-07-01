{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

-- | Functions for implementing PFPL Dynamics-inspired eval.

module Godel.Eval where

data Eval a
  = Step a
  | Value
    deriving (Show, Functor)

-- | Same as 'Data.Maybe.maybe'.
eval :: b -> (a -> b) -> Eval a -> b
eval value step = \case
  Step s -> step s
  Value -> value

run :: (a -> Eval a) -> a -> a
run op e = eval e (run op) (op e)
