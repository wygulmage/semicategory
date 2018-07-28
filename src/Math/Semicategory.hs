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

-- Good work-around with no obviously better design for built-in method inlining rules (https://ghc.haskell.org/trac/ghc/ticket/10595):
__RULE__compose__ :: Semicategory c ⇒ c y z → c x y → c x z
__RULE__compose__ = (◃)
{-# INLINE [1] __RULE__compose__ #-}
{-# RULES
  "SPJ/compose" ∀ a b. a ◃ b = __RULE__compose__ a b;
  "SPJ/flipped compose" ∀ a b. a ▹ b = __RULE__compose__ b a;
  #-}
{-# ANN __RULE__compose__ "HLint: ignore" #-}

--- Opposite Semicategory ---
instance (Semicategory c, Opposite c ~ Flip c) ⇒ Semicategory (Flip c) where
  -- type Object (Flip c) = Object c
  opposite :: Flip c x y → c y x
  opposite = unFlip
  Flip f ◃ Flip g = Flip (f ▹ g)

--- Isomorphisms in a semicategory ---
instance Semicategory c ⇒ Semicategory (Iso c) where
  -- type Object (Iso c) = Object c
  opposite (Iso u r) = Iso r u
  Iso u1 r1 ▹ Iso u2 r2 = Iso (u1 ◃ u2) (r1 ▹ r2)



--- Unconstrained object ---
class EveryObject o
instance EveryObject o


--- Examples ---

instance Semicategory (,) where
  -- type Object (,) = EveryObject
  (l, _) ▹ (_, r) = (l, r)


instance Semicategory (→) where
  -- type Object (→) = EveryObject
  (f ◃ g) x = f (g x)
