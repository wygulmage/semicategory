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

data NT :: ∀ i j. Arrow1 i → Arrow1 j → Arrow1 (i → j) where
  NT ::
    (Functor d c f, Functor d c g) ⇒
    {runNT :: ∀ (x :: i). c (f x) (g x)}
    → NT d c f g

class
  (Category d, Category c) ⇒
  Functor (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j)
  where
  fmap :: d x y → c (f x) (f y)

class
  Functor (Opposite c) (NT c (→)) c ⇒
  Category (c :: Arrow1 i)
  where
  source :: c x y → c x x
  target :: c x y → c y y
  (◃) :: c y z → c x y → c x z

  -- (mostly) internal and defaults:
  a ◃ b = runNT ((fmap :: Opposite c x y → NT c (→) (c x) (c y))
                   (opposite b)) a
  opposite :: c x y → Opposite c y x
  default opposite :: Opposite c ~ Flip c ⇒ c x y → Opposite c y x
  opposite = Flip



----- Instances -----


-- natural transformations:

instance Functor (Flip (NT d c)) (NT (NT d c) (→)) (NT d c) where
  fmap (Flip (NT a)) = NT (\(NT b) → NT (b ◃ a))

instance Functor (NT d c) (→) (NT d c f) where
  fmap = (◃)

instance Category (NT d c) where
  source = source
  target = target
  NT b ◃ NT a = NT (b ◃ a)


-- flipped arrows:

instance (Category c, Opposite c ~ Flip c) ⇒ Category (Flip c) where
  source (Flip a) = Flip (target a)
  target (Flip a) = Flip (source a)
  opposite = unFlip
  Flip b ◃ Flip a = Flip (a ◃ b)

instance (Category c, Category (Flip c)) ⇒ Functor c (NT (Flip c) (→)) (Flip c) where
  fmap a = NT (◃ Flip a)

instance (Category c, Category (Flip c)) ⇒ Functor (Flip c) (→) (Flip c y) where
  fmap = (◃)


-- functions:

instance Category (→) where
  source _ x = x
  target _ y = y
  (g ◃ f) x = g (f x)

instance Functor (Flip (→)) (NT (→) (→)) (→) where
  fmap (Flip a) = NT (◃ a)

instance Functor (→) (→) ((→) x) where
  fmap = (◃)
