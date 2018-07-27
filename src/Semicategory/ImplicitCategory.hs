{-# LANGUAGE
  NoImplicitPrelude
  ,
  UnicodeSyntax
  ,
  ExplicitNamespaces
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
  GADTs
  ,
  Safe
  #-}

module Semicategory.ImplicitCategory (
  module Semicategory.ImplicitSemicategory
  ,
  Category(..)
  ) where

import Semicategory.ImplicitSemicategory

class Semicategory c ⇒ Category c where
  id :: c x x

instance Category c ⇒ Category (Iso c) where
  id = Iso id id

instance (Category c, Flip c ~ Opposite c) ⇒ Category (Flip c) where
  id = Flip id


--- Examples ---

instance Category (→) where
  id x = x
