{-# LANGUAGE
  UnicodeSyntax
  ,
  TypeInType
  #-}

module Math.Iso (
  Iso(..)
  ) where

import Data.Kind (Type)

data Iso (c :: i → i → Type) x y = Iso {un :: c y x, run :: c x y}
