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

module Semicategory.Category (
  module Semicategory.Semicategory
  ,
  Category(..)
  ) where

import Semicategory.Semicategory

class Semicategory c ⇒ Category c where
  id :: c x x

instance Category c ⇒ Category (Iso c) where
  id = Iso id id

instance (Category c, Flip c ~ Opposite c) ⇒ Category (Flip c) where
  id = Flip id


--- Examples ---

instance Category (→) where
  id x = x
