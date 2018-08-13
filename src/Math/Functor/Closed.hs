{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
  ,
  TypeInType
  ,
  TypeFamilies
  ,
  ConstraintKinds
  ,
  MultiParamTypeClasses
  ,
  FlexibleContexts
  ,
  FlexibleInstances
  ,
  UndecidableSuperClasses
  ,
  UndecidableInstances -- for Flip'd Monoidal categories
  ,
  FunctionalDependencies
  #-}

module Math.Functor.Closed (
  Semiclosed(..)
  ,
  Closed(..)
  ,
  Coclosed(..)
  ) where

import Math.Functor.Monoidal

class Semimonoidal c f ⇒ Semiclosed (c :: Arrow1 i) f | c → f where
  type Power c :: i → i → i
  curry :: Iso (→) (c (f x y) z) (c x (Power c y z))

class (Semiclosed c f, Monoidal c f) ⇒ Closed c f where
  apply :: c (f (Power c x y) x) y

class (Semiclosed c f, Monoidal c f) ⇒ Coclosed c f where
  coapply :: c y (f (Power c x y) x)


----- Instances -----

--- Isomorphisms:

-- instance Semiclosed c f ⇒ Semiclosed (Iso c) f where
--   type Power (Iso c) = Power c
--   -- curry :: Iso (→) (Iso c (f x y) z) (Iso c x (Power c y z))
--   -- curry :: Iso (Iso (c z (f x y)) (c (f x y) z)) (Iso (c (Power c y z) x) (c x (Power c y z)))
--   curry = Iso
--     (\(Iso u r) → Iso (un curry u) (run curry r))
--     (\(Iso u r) → Iso (run curry u) (un curry r))


--- Functions:

instance Semiclosed (→) (,) where
  type Power (→) = (→)
  curry = Iso
    (\f (x, y) → f x y)
    (\f x y → f (x, y))

instance Closed (→) (,) where
  apply (f, x) = f x
