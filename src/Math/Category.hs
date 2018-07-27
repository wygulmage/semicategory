{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
  ,
  TypeInType
  ,
  TypeFamilies
  ,
  FlexibleInstances
  ,
  FlexibleContexts
  ,
  DefaultSignatures
  ,
  MultiParamTypeClasses
  ,
  RankNTypes
  ,
  FunctionalDependencies
  ,
  InstanceSigs
  ,
  ConstraintKinds
 #-}

module Math.Category (
  Category(..)
  ,
  module Math.Semicategory
  ) where

import Math.Semicategory

--- Category ---
class Semicategory c ⇒ Category (c :: Arrow1 o) where
  id :: c x x

--- Opposite Category ---
instance (Category c, Opposite c ~ Flip c) ⇒ Category (Flip c) where
  id = Flip id

--- Isomorphisms in a category ---
instance Category c ⇒ Category (Iso c) where
  id = Iso id id
  -- Really this should only require Semicategory c, and should exclude all objects that don't have arrows. Every Iso gives an identity.

--- Category of Functions ---
instance Category (→) where
  id x = x
