module Godel.Typecheck where

import Data.Map (Map)
import qualified Data.Map as Map

data Mismatch ty
  = Mismatch String ty ty
    deriving (Show)

type Context name ty
  = Map name ty

emptyContext :: Context name ty
emptyContext = Map.empty

match rule l r next =
  if l /= r
  then error (show (Mismatch rule l r))
  else next

resolve :: Ord name => Context name ty -> name -> ty
resolve context n =
  maybe (error "context fail") id (Map.lookup n context)

intro :: Ord name => Context name ty -> name -> ty -> Context name ty
intro c n t = Map.insert n t c
