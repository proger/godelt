module Godel.Typecheck where

import Prelude hiding (lookup)
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

lookup :: Ord name => Context name ty -> name -> Maybe ty
lookup = flip Map.lookup

resolve :: Ord name => Context name ty -> name -> ty
resolve context n =
  maybe (error "context fail") id (lookup context n)

intro :: Ord name => name -> ty -> Context name ty -> Context name ty
intro = Map.insert

refresh :: t2 -> (t2 -> t, t1) -> (t, t1)
refresh context (f, t) = (f context, t)
