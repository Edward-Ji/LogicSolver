module Util where

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM bAction t f = do
  b <- bAction
  if b then t else f
