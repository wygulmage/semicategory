{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
  ,
  TypeInType
  -- PolyKinds
  ,
  ScopedTypeVariables
  ,
  TypeFamilies
  ,
  RankNTypes
  ,
  ConstraintKinds
  ,
  TypeOperators
  ,
  MultiParamTypeClasses
  ,
  FlexibleContexts
  ,
  FlexibleInstances
  ,
  DefaultSignatures
  ,
  GADTs
  ,
  UndecidableSuperClasses
  ,
  FunctionalDependencies
  #-}

module Math.Functor.Terminal where

import Math.Functor.Functor
import Data.Void (Void, absurd)

class Category c ⇒ Terminal c where
  type Ob1 c
  arrow1 :: c x (Ob1 c)

class Category c ⇒ Coterminal c where
  type Ob0 c
  arrow0 :: c (Ob0 c) x

idS :: Terminal c ⇒ c x x
idS = source arrow1

idT :: Coterminal c ⇒ c x x
idT = target arrow0

instance (Terminal c, Opposite c ~ Flip c) ⇒ Coterminal (Flip c) where
  type Ob0 (Flip c) = Ob1 c
  arrow0 = Flip arrow1

instance (Coterminal c, Opposite c ~ Flip c) ⇒ Terminal (Flip c) where
  type Ob1 (Flip c) = Ob0 c
  arrow1 = Flip arrow0

instance Terminal (→) where
  type Ob1 (→) = ()
  arrow1 _ = ()

instance Coterminal (→) where
  type Ob0 (→) = Void
  arrow0 = absurd
