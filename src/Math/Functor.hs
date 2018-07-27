{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
  ,
  ScopedTypeVariables
  ,
  TypeInType
  ,
  TypeFamilies
  ,
  ConstrainedClassMethods
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
  ,
  GADTs
 #-}

module Math.Functor
  where

import Math.Category

class (Category (d :: Arrow1 i), Category (c :: Arrow1 j)) ⇒
      Functor d c (f :: i → j) where
  fmap :: d x y → c (f x) (f y)

data NT d c f g where
  NT :: (Category d, Category c) ⇒ { runNT :: ∀ x. c (f x) (g x) } → NT d c f g

instance Semicategory (NT d c) where
  type Object (NT d c) = Functor d c
  NT a ▹ NT b = NT (a ▹ b)

instance ∀ d c. (Category d, Category c) ⇒ Category (NT (d :: Arrow1 i) (c :: Arrow1 j)) where
  id :: ∀ (f :: i → j). Functor d c f ⇒ NT d c f f
  id = NT id

instance Functor (Flip (NT d c)) (NT (NT d c) (→)) (NT d c) where
  fmap (Flip t) = NT (t ▹)

instance Functor (NT d c) (→) (NT d c f) where
  fmap = (◃)
