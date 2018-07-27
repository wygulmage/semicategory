
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
  #-}

module Category.Semigroupoid (
  Arrow1
  ,
  Semigroupoid(..)
  ,
  Category(..)
  ,
  Groupoid(..)
  ,
  EveryObject
  ,
  Flip(..)
  ,
  Opposite
  ) where

import Data.Kind (Constraint, Type)
import Category.Flip

type Arrow1 o = o -> o -> Type

class Semigroupoid (c :: Arrow1 k) where
  type Object c :: k -> Constraint
  opposite :: c x y -> Opposite c y x
  default opposite :: (Opposite c ~ Flip c) => c x y -> Opposite c y x
  opposite = Flip
  (▹) :: c x y → c y z → c x z
  f ▹ g = g ◃ f
  (◃) :: c y z → c x y → c x z
  g ◃ f = f ▹ g

--- Opposite Semigroupoid ---
instance (Semigroupoid c, Opposite c ~ Flip c) ⇒ Semigroupoid (Flip c) where
  type Object (Flip c) = Object c
  opposite = unFlip
  Flip f ◃ Flip g = Flip (f ▹ g)


--- Category ---
class Semigroupoid c ⇒ Category c where
  id :: c x x

--- Opposite Category ---
instance (Category c, Opposite c ~ Flip c) ⇒ Category (Flip c) where
  id = Flip id


--- Groupoid ---
class Category c ⇒ Groupoid c where
  invert :: c x y → c y x

--- Unconstrained object ---
class EveryObject o
instance EveryObject o


--- Examples ---

instance Semigroupoid (,) where
  type Object (,) = EveryObject
  (l, _) ▹ (_, r) = (l, r)

instance Semigroupoid (→) where
  type Object (→) = EveryObject
  (f ◃ g) x = f (g x)

instance Category (→) where
  id x = x
