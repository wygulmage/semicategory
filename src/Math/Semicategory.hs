{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
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
  InstanceSigs
  #-}

module Math.Semicategory (
  Arrow1
  ,
  Semicategory(..)
  ,
  Groupoid(..)
  ,
  EveryObject
  ,
  Iso(..)
  ,
  Flip(..)
  ,
  Opposite
  ) where

import Data.Kind (Constraint, Type)
-- import Category.Flip

type Arrow1 o = o -> o -> Type

newtype Flip (c :: Arrow1 o) y x = Flip { unFlip :: c x y }

data Iso (c :: Arrow1 o) x y = Iso { un :: c y x, run :: c x y }

type family Opposite (c :: Arrow1 o) :: Arrow1 o where
  Opposite (Iso c) = Iso c -- no need for another wrapper
  Opposite (Flip c) = c
  Opposite c = Flip c

class Semicategory (c :: Arrow1 k) where
  type Object c :: k -> Constraint
  opposite :: c x y -> Opposite c y x
  default opposite :: (Opposite c ~ Flip c) => c x y -> Opposite c y x
  opposite = Flip
  (▹) :: c x y → c y z → c x z
  f ▹ g = g ◃ f
  (◃) :: c y z → c x y → c x z
  g ◃ f = f ▹ g

--- Opposite Semicategory ---
instance (Semicategory c, Opposite c ~ Flip c) ⇒ Semicategory (Flip c) where
  type Object (Flip c) = Object c
  opposite :: Flip c x y → c y x
  opposite = unFlip
  Flip f ◃ Flip g = Flip (f ▹ g)

--- Isomorphisms in a semicategory ---
instance Semicategory c ⇒ Semicategory (Iso c) where
  type Object (Iso c) = Object c
  opposite (Iso u r) = Iso r u
  Iso u1 r1 ▹ Iso u2 r2 = Iso (u1 ◃ u2) (r1 ▹ r2)



--- Groupoid ---
class Semicategory c ⇒ Groupoid c where
  invert :: c x y → c y x

--- Opposite Groupoid ---
instance (Groupoid c, Opposite c ~ Flip c) ⇒ Groupoid (Flip c) where
  invert (Flip a) = Flip (invert a)

--- Isomorphisms in a groupoid ---
instance Semicategory c ⇒ Groupoid (Iso c) where
  invert = opposite

--- Unconstrained object ---
class EveryObject o
instance EveryObject o


--- Examples ---

instance Semicategory (,) where
  type Object (,) = EveryObject
  (l, _) ▹ (_, r) = (l, r)

instance Groupoid (,) where
  invert (x, y) = (y, x)

instance Semicategory (→) where
  type Object (→) = EveryObject
  (f ◃ g) x = f (g x)
