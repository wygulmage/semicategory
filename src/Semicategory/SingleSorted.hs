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
  RankNTypes
  ,
  MultiParamTypeClasses
  ,
  FlexibleInstances
  ,
  FlexibleContexts
  ,
  DefaultSignatures
  ,
  -- UndecidableInstances -- CatsObject
  -- ,
  -- UndecidableSuperClasses -- CatsObject
  -- ,
  InstanceSigs
  ,
  GADTs
  ,
  TypeOperators
  ,
  Safe
  #-}

module Semicategory.SingleSorted
  where

import Data.Kind (Type)
import Semicategory.Opposite
import Semicategory.Semicategory (Arrow1)

type family Source a where
  Source (c x y) = c x x

type family Target a where
  Target (c x y) = c y y

-- type family Object (c :: o → o → Type) x where
--   Object c x = c x x

class Category (c :: Arrow1 o) where
  source :: c x y → Source (c x y)
  target :: c x y → Target (c x y)
  compose :: c y z → c x y → c x z

instance Category (→) where
  source :: (x → y) → x → x
  source _ x = x
  target :: (x → y) → y → y
  target _ y = y
  compose :: (y → z) → (x → y) → x → z
  compose f g x = f (g x)

instance (Category c, Flip c ~ Opposite c) ⇒ Category (Flip c) where
  source (Flip a) = Flip (target a)
  target (Flip a) = Flip (source a)
  compose (Flip f) (Flip g) = Flip (compose g f)

instance Category c ⇒ Category (Iso c) where
  source :: Iso c x y → Iso c x x
  source (Iso u r) = Iso (target u) (source r)
  target :: Iso c x y → Iso c y y
  target (Iso u r) = Iso (source u) (target r)
  compose (Iso u2 r2) (Iso u1 r1) = Iso (compose u1 u2) (compose r2 r1)

instance Category (,) where
  source (x, _) = (x, x)
  target (_, y) = (y, y)
  compose (_, z) (x, _) = (x, z)

class Category c ⇒ Groupoid c where
  invert :: c x y → c y x

instance Category c ⇒ Groupoid (Iso c) where
  invert (Iso u r) = Iso r u

class (Category d, Category c) ⇒ Functor d c f where
  fmap :: d x y → c (f x) (f y)

-- newtype NT d c f g = NT { runNT :: ∀ x. c (f x) (g x) }
data NT d c f g where
  NT ::
    (Category d, Category d) ⇒
    {runNT ::
        ∀ x.
        c (f x) (g x)} → NT d c f g

instance (Category d, Category c) ⇒ Category (NT d c) where
  source (NT t) = NT (source t)
  target (NT t) = NT (target t)
  compose (NT s) (NT t) = NT (compose s t)

instance (Category d, Category c) ⇒ Functor (Flip (NT d c)) (NT (NT d c) (→)) (NT d c) where
  fmap (Flip t) = NT (`compose` t)

instance (Category d, Category c) ⇒ Functor (NT d c) (→) (NT d c f) where
  fmap = compose

instance Functor (Flip (→)) (NT (→) (→)) (→) where
  fmap (Flip f) = NT (`compose` f)

instance Functor (→) (→) ((→) k) where
  fmap = compose
