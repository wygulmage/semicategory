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

module Semicategory.ExplicitCategory (
  module Semicategory.ExplicitSemicategory
  ,
  Category(..)
  ) where

import Semicategory.ExplicitSemicategory

class Semicategory c ⇒ Category c where
  id ::
    Object c x ⇒
    c x x

instance Category c ⇒ Category (Iso c) where
  id = Iso id id

instance (Category c, Flip c ~ Opposite c) ⇒ Category (Flip c) where
  id = Flip id


--- Examples ---

instance Category (→) where
  id x = x
