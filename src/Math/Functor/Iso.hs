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

module Math.Functor.Iso where

import Math.Functor.Functor
import Math.Functor.Terminal

data Iso :: ∀ i. Arrow1 i → Arrow1 i where
  Iso :: Category c ⇒ { un :: c y x, run :: c x y} → Iso c x y

instance Category (Iso c) where
  type Opposite (Iso c) = Iso c
  opposite (Iso u r) = Iso r u
  unOpposite = opposite
  source (Iso u r) = Iso (target u) (source r)
  target (Iso u r) = Iso (source u) (target r)
  Iso u2 r2 ◃ Iso u1 r1 = Iso (u1 ◃ u2) (r2 ◃ r1)

instance Functor (Iso c) (NT (Iso c) (→)) (Iso c) where
  fmap a = NT (◃ opposite a)

instance Functor (Iso c) (→) (Iso c k) where
  fmap = (◃)

instance (Terminal c, Coterminal c, Ob1 c ~ Ob0 c) ⇒ Terminal (Iso c) where
  type Ob1 (Iso c) = Ob1 c
  arrow1 = Iso arrow0 arrow1

instance (Terminal c, Coterminal c, Ob1 c ~ Ob0 c) ⇒ Coterminal (Iso c) where
  type Ob0 (Iso c) = Ob0 c
  arrow0 = Iso arrow1 arrow0
