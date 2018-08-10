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

module Math.Functor.Functor where

import Data.Kind (Type, Constraint)
import Data.Either (Either(..), either)
import qualified Data.List (map)


-- Arrows in a category:
type Arrow1 i = i → i → Type

-- Flipped arrows:
newtype Flip :: (i → j → Type) → j → i → Type where
  Flip :: {unFlip :: f x y} → Flip f y x

-- Opposite arrows:
type family Opposite (f :: i → j → Type) :: j → i → Type where
  Opposite (Flip f) = f
  Opposite f = Flip f

-- Natural transformations:
data NT :: ∀ i j. Arrow1 i → Arrow1 j → Arrow1 (i → j) where
  NT ::
    (Functor d c f, Functor d c g) ⇒
    {runNT :: ∀ (x :: i). c (f x) (g x)}
    → NT d c f g

-- Functors:
class
  (Category d, Category c) ⇒
  Functor (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j)
  | f d → c
  where
  fmap :: d x y → c (f x) (f y)

-- Categories:
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

instance Category (NT d c) where
  source = source
  target = target
  NT b ◃ NT a = NT (b ◃ a)

instance Functor (Flip (NT d c)) (NT (NT d c) (→)) (NT d c) where
  fmap (Flip (NT a)) = NT (\(NT b) → NT (b ◃ a))

instance Functor (NT d c) (→) (NT d c f) where
  fmap = (◃)


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


--- Instances I'd Rather Not Put Here But Which Would Otherwise Be Orphans ---

instance Functor (→) (NT (→) (→)) (,) where
  fmap a = NT (\(x, k) → (a x, k))

instance Functor (→) (→) ((,) k) where
  fmap a (k, y) = (k, a y)

instance Functor (→) (NT (→) (→)) Either where
  fmap a = NT (either (Left ◃ a) Right)

instance Functor (→) (→) (Either k) where
  fmap a = either Left (Right ◃ a)

instance Functor (→) (→) [] where
  fmap = Data.List.map
