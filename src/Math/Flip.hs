{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
  ,
  TypeInType
  ,
  GADTSyntax
  #-}

module Math.Flip (
  Flip(..)
  ) where

import Data.Kind (Type)

newtype Flip :: (i → j → Type) → j → i → Type where
  Flip :: {unFlip :: f x y} → Flip f y x
