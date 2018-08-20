{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
  ,
  TypeInType
  ,
  ScopedTypeVariables
  ,
  TypeFamilies
  ,
  RankNTypes
  ,
  MultiParamTypeClasses
  ,
  FlexibleContexts
  ,
  FlexibleInstances
  ,
  GADTs
  ,
  UndecidableSuperClasses
  #-}

module Math.Category.Iso (
  Iso(..)
  ,
  isoFlip
  ) where

import Math.Category.Functor
import Math.Category.Terminal

data Iso :: ∀ i. Arrow1 i → Arrow1 i where
  Iso :: Category c ⇒
    { un :: c y x, run :: c x y} → Iso c x y

isoFlip ::
  (Opposite c ~ Flip c) ⇒
  Iso c u r → Iso (Flip c) u r
isoFlip (Iso u r) = Iso (Flip r) (Flip u)

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

instance Functor d c f ⇒ Functor (Iso d) (Iso c) f where
  fmap (Iso u r) = Iso (fmap u) (fmap r)

instance Bifunctor d1 d2 c f ⇒ Functor (Iso d1) (NT (Iso d2) (Iso c)) f where
  fmap (Iso u r) = case (map u, map r) of
    (NT t, NT s) → NT (Iso t s)
    where
      map :: d1 x y → NT d2 c (f x) (f y)
      map = fmap

instance
  (Terminal c, Coterminal c, Ob1 c ~ Ob0 c) ⇒
  Terminal (Iso c) where
  type Ob1 (Iso c) = Ob1 c
  arrow1 = Iso arrow0 arrow1

instance
  (Terminal c, Coterminal c, Ob1 c ~ Ob0 c) ⇒
  Coterminal (Iso c) where
  type Ob0 (Iso c) = Ob0 c
  arrow0 = Iso arrow1 arrow0
