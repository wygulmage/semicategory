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
  EveryObject
  ,
  Iso(..)
  ,
  Flip(..)
  ,
  Opposite
  ) where

import Data.Kind (
  -- Constraint
  -- ,
  Type
  )
import Math.Opposite

type Arrow1 o = o -> o -> Type

-- newtype Flip (c :: Arrow1 o) y x = Flip { unFlip :: c x y }

-- data Iso (c :: Arrow1 o) x y = Iso { un :: c y x, run :: c x y }

-- type family Opposite (c :: Arrow1 o) :: Arrow1 o where
--   Opposite (Iso c) = Iso c -- no need for another wrapper
--   Opposite (Flip c) = c
--   Opposite c = Flip c


class Semicategory (c :: Arrow1 k) where
  -- type Object c :: k -> Constraint
  opposite :: c x y -> Opposite c y x
  default opposite :: (Opposite c ~ Flip c) => c x y -> Opposite c y x
  opposite = Flip
  (▹) :: c x y → c y z → c x z
  f ▹ g = g ◃ f
  (◃) :: c y z → c x y → c x z
  g ◃ f = f ▹ g

-- Laws:
-- ∀ a b. a ▹ b ≡ b ◃ a
-- ∀ a b c. c ◃ (b ◃ a) ≡ (c ◃ b) ◃ a


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


class Category c ⇒ Groupoid c where
  invert :: c x y → c y x

-- Laws:
-- ∀ a. invert a ◃ a ≡ target a
-- ∀ a. a ◃ invert a ≡ source a


--- Flip the Arrows ---

instance (Semicategory c, Opposite c ~ Flip c) ⇒ Semicategory (Flip c) where
  -- type Object (Flip c) = Object c
  opposite :: Flip c x y → c y x
  opposite = unFlip
  Flip f ◃ Flip g = Flip (f ▹ g)

instance (Category c, Opposite c ~ Flip c) ⇒ Category (Flip c) where
  source (Flip a) = Flip (target a)
  target (Flip a) = Flip (source a)

instance (Groupoid c, Opposite c ~ Flip c) ⇒ Groupoid (Flip c) where
  invert (Flip a) = Flip (invert a)


--- Cores ---

instance Semicategory c ⇒ Semicategory (Iso c) where
  -- type Object (Iso c) = Object c
  opposite (Iso u r) = Iso r u
  Iso u1 r1 ▹ Iso u2 r2 = Iso (u1 ◃ u2) (r1 ▹ r2)

instance Semicategory c ⇒ Category (Iso c) where
  source (Iso u r) = Iso (u ◃ r) (u ◃ r)
  target (Iso u r) = Iso (r ◃ u) (r ◃ u)

instance Semicategory c ⇒ Groupoid (Iso c) where
  invert = opposite


--- Unconstrained object ---
class EveryObject o
instance EveryObject o


--- Functions ---

instance Semicategory (→) where
  -- type Object (→) = EveryObject
  (f ◃ g) x = f (g x)

instance Category (→) where
  source _ x = x
  target _ y = y


--- Tuple Groupoid ---

instance Semicategory (,) where
  -- type Object (,) = EveryObject
  (l, _) ▹ (_, r) = (l, r)

instance Category (,) where
  source (x, _) = (x, x)
  target (_, y) = (y, y)

instance Groupoid (,) where
  invert (x, y) = (y, x)


----- RULES -----
-- 'Good work-around with no obviously better design' for built-in method inlining rules, courtesy of the master himself (https://ghc.haskell.org/trac/ghc/ticket/10595):

__RULE__compose__ :: Semicategory c ⇒ c y z → c x y → c x z
__RULE__compose__ = (◃)
{-# INLINE [1] __RULE__compose__ #-}
{-# RULES
  "SPJ/compose" (◃) = __RULE__compose__;
  "SPJ/flipped compose" ∀ a b. a ▹ b = __RULE__compose__ b a;
  #-}
{-# ANN __RULE__compose__ "HLint: ignore" #-}

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

__RULE__invert__ :: Groupoid c ⇒ c x y → c y x
__RULE__invert__ = invert
{-# ANN __RULE__invert__ "HLint: ignore" #-}
{-# INLINE [1] __RULE__invert__ #-}
{-# RULES "SPJ/invert" invert = __RULE__invert__ #-}

{-# RULES
  "SPJ/source/source" ∀ a. __RULE__source__ (__RULE__source__ a) = __RULE__source__ a
  ;
  "SPJ/target/source" ∀ a. __RULE__target__ (__RULE__source__ a) = __RULE__source__ a
  ;
  "SPJ/target/target" ∀ a. __RULE__target__ (__RULE__target__ a) = __RULE__target__ a
  ;
  "SPJ/source/target" ∀ a. __RULE__source__ (__RULE__target__ a) = __RULE__target__ a
  ;
  "SPJ/compose/source" ∀ a. a ◃ __RULE__source__ a = a;
  ;
  "SPJ/compose/target" ∀ a. __RULE__target__ a ◃ a = a
  ;
  "SPJ/source/compose" ∀ a b. __RULE__source__ (__RULE__compose__ a b) = __RULE__source__ a
  ;
  "SPJ/target/compose" ∀ a b. __RULE__target__ (__RULE__compose__ a b) = __RULE__target__ b
  ;
  "SPJ/invert/target" ∀ a. __RULE__invert__ a ◃ a = __RULE__target__ a
  ;
  "SPJ/invert/source" ∀ a. a ◃ __RULE__invert__ a = __RULE__source__ a
  #-}
