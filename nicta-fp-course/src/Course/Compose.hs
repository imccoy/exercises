{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Course.Compose where

import Course.Core
import Course.Functor
import Course.Applicative
import Course.Monad

-- Exactly one of these exercises will not be possible to achieve. Determine which.

newtype Compose f g a =
  Compose (f (g a))

-- Implement a Functor instance for Compose
instance (Functor f, Functor g) =>
    Functor (Compose f g) where
  f <$> (Compose fga) = Compose $ (f <$>) <$> fga


instance (Applicative f, Applicative g) =>
  Applicative (Compose f g) where
  pure = Compose . pure . pure
  (Compose fgf) <*> (Compose fga) = Compose $ (\f a -> f <*> a) <$> fgf <*> fga

instance (Monad f, Monad g) =>
  Monad (Compose f g) where
  (=<<) = error "NOPE"
