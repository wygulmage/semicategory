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
  RankNTypes
  ,
  ScopedTypeVariables
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
  ) where

import Math.Functor.Monoidal
import Math.Functor.Adjoint

class (Semimonoidal c (Tensor c))  ⇒ Semiclosed (c :: Arrow1 i) where
  type Power c :: i → i → i
  type Tensor c ::  i → i → i
  curry :: Iso (→) (c (Tensor c x y) z) (c x (Power c y z))

class (Semiclosed c, Monoidal c (Tensor c)) ⇒ Closed (c :: Arrow1 i) where
  apply :: c (Tensor c (Power c x y) x) y
  -- apply = case unitL of Iso u r → un curry (u ◃ r) -- need to help the type checker a bit
  apply = un curry idPower
    where
      unitPower :: Iso c (Power c x y) (Tensor c (Power c x y) (Unit (Tensor c)))
      unitPower = unitR
      idPower :: c (Power c x y) (Power c x y)
      idPower = un unitPower ◃ run unitPower

instance (Semiclosed c, Monoidal c (Tensor c)) ⇒ Closed (c :: Arrow1 i)

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

instance Semiclosed (→) where
  type Power (→) = (→)
  type Tensor (→) = (,)
  curry = Iso
    (\f → un adjunct f ◃ swap)
    (\f → run adjunct (f ◃ swap))
