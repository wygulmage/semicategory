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
  #-}

module Math.Functor.Functor where

import Data.Kind (Type, Constraint)

type Arrow1 i = i → i → Type

newtype Flip :: (i → j → Type) → j → i → Type where
  Flip :: {unFlip :: f x y} → Flip f y x

type family Opposite (f :: i → j → Type) :: j → i → Type where
  Opposite (Flip f) = f
  Opposite f = Flip f

-- data NT :: Arrow1 i → Arrow1 j → Arrow1 (i → j) where
--   NT ::
--     (Functor d c f, Functor d c g) ⇒
--     ∀ x. c (f x) (g x)
--     → NT d c f g

-- data NT (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j) (g :: i → j) where
--   NT ::
--     (Functor d c f, Functor d c g) ⇒
--     ∀ (x :: i). c (f x) (g x)
--     → NT d c f g

-- data NT (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j) (g :: i → j) where
--   NT :: ∀ d c f g.
--     (Functor d c f, Functor d c g) ⇒
--     ∀ (x :: i). (c :: Arrow1 j) ((f :: i → j) x) ((g :: i → j) x)
--     → NT (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j) (g :: i → j)

-- data NT d c f g where
--   NT ::
--     ∀ (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j) (g :: i → j).
--     (Functor d c f, Functor d c g) ⇒
--     ∀ (x :: i). c (f x) (g x)
--     → NT d c f g

-- data NT :: Arrow1 i → Arrow1 j → Arrow1 (i → j) where
--   NT ::
--     ∀ (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j) (g :: i → j).
--     (Functor d c f, Functor d c g) ⇒
--     ∀ x. c (f x) (g x)
--     → NT d c f g

data NT :: ∀ i j. Arrow1 i → Arrow1 j → Arrow1 (i → j) where
  NT ::
    (Functor d c f, Functor d c g) ⇒
    {runNT :: ∀ (x :: i). c (f x) (g x)}
    → NT d c f g

-- data NT (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j) (g :: i → j) where
--   NT ::
--     (Functor d c f, Functor d c g) ⇒
--     {runNT :: ∀ x. c (f x) (g x)}
--     → NT d c f g

class
  (Category d, Category c) ⇒
  Functor (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j)
  -- Functor d c f
  where
  fmap :: d x y → c (f x) (f y)

class
  Functor (Opposite c) (NT c (→)) c ⇒
  Category (c :: Arrow1 i)
  -- Category c
  where
  source :: c x y → c x x
  target :: c x y → c y y