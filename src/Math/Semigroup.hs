{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
  ,
  TypeInType
  ,
  TypeFamilies
  ,
  DefaultSignatures
  ,
  ConstraintKinds
  #-}

module Math.Semigroup (
  Semigroup(..)
  ,
  Monoid(..)
  ,
  Anihilative(..)
  ,
  Commutative
  ,
  RightCancellative(..)
  ,
  LeftCancellative(..)
  ,
  Cancellative
  ,
  Group(..)
  ) where

{--- About Properties ---
Inverse and compliment are somewhat dual. Inverse and compliment are in the best case both involutions. (inv x) · x = the identity element. (not x) · x = the anihilative element.

--}

class Semigroup s where
  (·) :: s → s → s

class Semigroup m ⇒ Monoid m where
  identity :: m

class Semigroup a ⇒ Anihilative a where
  nihil :: a
-- Laws:
-- ∀ x. x · nihil = nihil
-- ∀ x. nihil · x = nihil

class Semigroup s ⇒ Commutative s
-- Laws:
-- ∀ x y. x · y = y · x

class Monoid s ⇒ LeftCancellative s where
  (\\) :: s → s → s
  default (\\) :: Group s ⇒ s → s → s
  x \\ y = negate x · y
-- Laws:
-- ∀ x y. x \\ (x · y) = y

class Monoid s ⇒ RightCancellative s where
  (//) :: s → s → s
  default (//) :: Group s ⇒ s → s → s
  x // y = x · negate y
-- Laws:
-- ∀ x y. (x · y) // y = x

type Cancellative s = (LeftCancellative s, RightCancellative s)


class Cancellative s ⇒ Group s where
  negate :: s → s
-- Laws:
-- ∀ x y. negate x · x · y = y
-- ∀ x y. x · y · negate y = x

----- RULES -----
__RULE__dot__ :: Semigroup s ⇒ s → s → s
__RULE__dot__ = (·)
{-# INLINE [1] __RULE__dot__ #-}
{-# RULES "SPJ/RULE__dot" (·) = __RULE__dot__ #-}

__RULE__identity__ :: Monoid m ⇒ m
__RULE__identity__ = identity
{-# INLINE [1] __RULE__identity__ #-}
{-# RULES "SPJ/RULE__identity" identity = __RULE__identity__ #-}

__RULE__nihil__ :: Anihilative a ⇒ a
__RULE__nihil__ = nihil
{-# INLINE [1] __RULE__nihil__ #-}
{-# RULES "SPJ/RULE__nihil" nihil = __RULE__nihil__ #-}

__RULE__leftCancel__ :: LeftCancellative s ⇒ s → s → s
__RULE__leftCancel__ = (\\)
{-# INLINE [1] __RULE__leftCancel__ #-}
{-# RULES "SPJ/RULE__leftCancel" (\\) = __RULE__leftCancel__ #-}

__RULE__rightCancel__ :: RightCancellative s ⇒ s → s → s
__RULE__rightCancel__ = (//)
{-# INLINE [1] __RULE__rightCancel__ #-}
{-# RULES "SPJ/RULE__rightCancel" (//) = __RULE__rightCancel__ #-}

__RULE__negate__ :: Group s ⇒ s → s
__RULE__negate__ = negate
{-# INLINE [1] __RULE__negate__ #-}
{-# RULES "SPJ/RULE__negate" negate = __RULE__negate__ #-}

{-# RULES
  "associativity" ∀ x y z. x `__RULE__dot__` (y `__RULE__dot__` z) = (x `__RULE__dot__` y) `__RULE__dot__` z
  ;
  "left identity" ∀ x. __RULE__identity__ `__RULE__dot__` x = x
  ;
  "right identity" ∀ x. x `__RULE__dot__` __RULE__identity__ = x
  ;
  "left anihilation" ∀ x. __RULE__nihil__ `__RULE__dot__` x = __RULE__nihil__
  ;
  "right anihilation" ∀ x. __RULE__nihil__ `__RULE__dot__` x = __RULE__nihil__
  ;
  "left cancellation" ∀ x y. x `__RULE__leftCancel__` (x `__RULE__dot__` y) = y
  ;
  "right cancellation" ∀ x y. (x `__RULE__dot__` y) `__RULE__rightCancel__` y = x
  ;
  "left inverse" ∀ x y. __RULE__negate__ x `__RULE__dot__` x `__RULE__dot__` y = y
  ;
  "right inverse" ∀ x y. x `__RULE__dot__` y `__RULE__dot__` __RULE__negate__ y = x
  #-}
