{-# LANGUAGE
  UnicodeSyntax
  ,
  TypeInType
  #-}

module Data.Flip (
  Flip(..)
  ) where

import Data.Kind (Type)

newtype Flip (a :: i → j → Type) y x = Flip {unFlip :: a x y}
