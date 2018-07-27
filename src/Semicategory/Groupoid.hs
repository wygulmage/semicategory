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

module Semicategory.Groupoid
  where

import Semicategory.Semicategory

class Semicategory c ⇒ Groupoid c where
  invert :: c x y → c y x

-- Groupoid c should require Category c. But in Haskell it may not be possible to create a Category instance for a category. For example, the isomorphisms in a semicategory form a category where (by definition) i :: Iso c x y gives id_x with run i >>> un i, and id_y with un i >>> run i, but there is no way to define id :: ∀ x. Iso c x x.
-- In a more theoretical framework this would fail, but in Haskell we get external definitions of equality.

instance Semicategory (Iso c) ⇒ Groupoid (Iso c) where
  invert = opposite

instance (Groupoid c, Flip c ~ Opposite c) ⇒ Groupoid (Flip c) where
  invert (Flip a) = Flip (invert a)

--- Examples ---

instance Groupoid (,) where
  invert (x, y) = (y, x)
