{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
  ,
  TypeInType
  ,
  TypeFamilies
  ,
  ConstraintKinds
  ,
  MultiParamTypeClasses
  ,
  FlexibleContexts
  ,
  FlexibleInstances
  ,
  UndecidableSuperClasses
  #-}

module Math.Functor.Unit (
  type Unit
  ) where

import Data.Either (Either)
import Data.Void (Void)

-- Monoidal unit up to isomorphism
type family Unit (f :: i → i → j) :: i

type instance Unit (,) = ()
type instance Unit Either = Void
