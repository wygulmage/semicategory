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
  -- ,
  -- DefaultSignatures
  -- ,
  -- MultiParamTypeClasses
  -- ,
  -- RankNTypes
  -- ,
  -- FunctionalDependencies
  ,
  InstanceSigs
  -- ,
  -- ConstraintKinds
 #-}

module Math.Category (
  Category(..)
  ,
  module Math.Semicategory
  ) where

import Math.Semicategory

--- Category ---
class Semicategory c ⇒ Category (c :: Arrow1 o) where
  source :: c x y → c x x
  target :: c x y → c y y

-- Laws:
-- source ◃ source ≡ source
-- target ◃ source ≡ source
-- target ◃ target ≡ target
-- source ◃ target ≡ target
-- source ◃ (a ◃ b) ≡ source a
-- target ◃ (a ◃ b) ≡ target b
-- a ◃ (source a) ≡ a
-- (target a) ◃ a ≡ a


--- Opposite Category ---
instance (Category c, Opposite c ~ Flip c) ⇒ Category (Flip c) where
  source (Flip a) = Flip (target a)
  target (Flip a) = Flip (source a)

--- Core of a semicategory ---
instance Semicategory c ⇒ Category (Iso c) where
  source (Iso u r) = Iso (u ◃ r) (u ◃ r)
  target (Iso u r) = Iso (r ◃ u) (r ◃ u)

--- Category of Functions ---
instance Category (→) where
  source _ x = x
  target _ y = y

--- Rectangular Category ---
instance Category (,) where
  source (x, _) = (x, x)
  target (_, y) = (y, y)


----- RULES -----
-- 'Good work-around with no obviously better design' for built-in method inlining rules, courtesy of the master himself (https://ghc.haskell.org/trac/ghc/ticket/10595):

__RULE__source__ :: Category c ⇒ c x y → c x x
__RULE__source__ = source
{-# ANN __RULE__source__ "HLint: ignore" #-}
{-# INLINE [1] __RULE__source__ #-}
{-# RULES "SPJ/source" source = __RULE__source__ #-}

__RULE__target__ :: Category c ⇒ c x y → c y y
__RULE__target__ = target
{-# ANN __RULE__target__ "HLint: ignore" #-}
{-# INLINE [1] __RULE__target__ #-}
{-# RULES "SPJ/target" target = __RULE__target__ #-}

{-# RULES
  "SPJ/source/source" ∀ a. __RULE__source__ (__RULE__source__ a) = __RULE__source__ a
  ;
  "SPJ/target/source" ∀ a. __RULE__target__ (__RULE__source__ a) = __RULE__source__ a
  ;
  "SPJ/target/target" ∀ a. __RULE__target__ (__RULE__target__ a) = __RULE__target__ a
  ;
  "SPJ/source/target" ∀ a. __RULE__source__ (__RULE__target__ a) = __RULE__target__ a
  ;
  -- "SPJ/source/compose" ∀ a b. __RULE__source__ (a ◃ b) = __RULE__source__ a
  -- ; -- Method dummies are not portable.
  -- "SPJ/target/compose" ∀ a b. __RULE__target__ (a ◃ b) = __RULE__target__ b
  -- ; -- Method dummies are not portable.
  "SPJ/compose/source" ∀ a. a ◃ __RULE__source__ a = a;
  ;
  "SPJ/compose/target" ∀ a. __RULE__target__ a ◃ a = a
  #-}
