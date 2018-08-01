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

module Math.Distributive (
  Distributive(..)
  ,
  Sum(..)
  ,
  Product(..)
  ) where

import Math.Semigroup

class Distributive r where
  (+), (*) :: r → r → r
-- Laws:
-- ∀ x y z. x * (y + z) = (x * y) + (x * z)
-- ∀ x y z. (x + y) * z = (x * z) + (y * z)

class Distributive r ⇒ Zeroed r where
  zero :: r
-- Laws:
-- ∀ x. x + zero = x
-- ∀ x. zero + x = x
-- Because of distributivity, ∀ x y. x * (0 + y) = (x * 0) + (x * y), so zero is an anihilative element for (*).

class Distributive r ⇒ Oned r where
  one :: r
-- Laws:
-- ∀ x. x * one = x
-- ∀ x. one * x = x

class Zeroed r ⇒ RightSubtractable r where
  (-) :: r → r → r
  default (-) :: Negative r ⇒ r → r → r
  x - y = x + neg y
-- Law:
-- ∀ x y. (x + y) - y = x

class Zeroed r ⇒ LeftSubtractable r where
  subtract :: r → r → r
  default subtract :: Negative r ⇒ r → r → r
  subtract x y = neg x + y
-- Law:
-- ∀ x y. subtract x (x + y) = y

class Oned r ⇒ RightDivision r where
  (/) :: r → r → r
  default (/) :: Reciprocated r ⇒ r → r → r
  x / y = x * reciprocal y
-- Law:
-- ∀ x y. (x * y) / y = x

class Oned r ⇒ LeftDivision r where
  divide :: r → r → r
  default divide :: Reciprocated r ⇒ r → r → r
  divide x y = reciprocal x * y
-- Law:
-- ∀ x y. divide x (x * y) = y

class (LeftSubtractable r, RightSubtractable r) ⇒ Negative r where
  neg :: r → r
  neg r = zero - r

class (LeftDivision r, RightDivision r) ⇒ Reciprocated r where
  reciprocal :: r → r
  reciprocal r = one / r


--- Derived Semigroup instances ---

newtype Sum o = Sum {getSum :: o}
newtype Product o = Product {getProduct :: o}

instance Distributive r ⇒ Semigroup (Sum r) where
  Sum x · Sum y = Sum (x + y)

instance Distributive r ⇒ Semigroup (Product r) where
  Product x · Product y = Product (x * y)

instance Zeroed r ⇒ Monoid (Sum r) where
  identity = Sum zero

instance Oned r ⇒ Monoid (Product r) where
  identity = Product one

instance Zeroed r ⇒ Anihilative (Product r) where
  nihil = Product zero

instance RightSubtractable r ⇒ RightCancellative (Sum r) where
  Sum x // Sum y = Sum (x - y)

instance RightDivision r ⇒ RightCancellative (Product r) where
  Product x // Product y = Product (x / y)

instance LeftSubtractable r ⇒ LeftCancellative (Sum r) where
  Sum x \\ Sum y = Sum (subtract x y)

instance LeftDivision r ⇒ LeftCancellative (Product r) where
  Product x \\ Product y = Product (divide x y)

instance Negative r ⇒ Group (Sum r) where
  negate (Sum x) = Sum (neg x)

----- RULES -----

__RULE__plus__ :: Distributive r ⇒ r → r → r
__RULE__plus__ = (+)
{-# INLINE [1] __RULE__plus__ #-}
{-# RULES "SPJ/RULE__plus" (+) = __RULE__plus__ #-}

__RULE__times__ :: Distributive r ⇒ r → r → r
__RULE__times__ = (*)
{-# INLINE [1] __RULE__times__ #-}
{-# RULES "SPJ/RULE__times" (*) = __RULE__times__ #-}

__RULE__zero__ :: Zeroed r ⇒ r
__RULE__zero__ = zero
{-# INLINE [1] __RULE__zero__ #-}
{-# RULES "SPJ/RULE__zero" zero = __RULE__zero__ #-}

{-# RULES
  "distributivity" ∀ x y z. (x `__RULE__times__` y) `__RULE__plus__` (z `__RULE__times__` y) = (x `__RULE__plus__` z) `__RULE__times__` y
  ;
  "additive associativity" ∀ w x y z. w `__RULE__plus__` (x `__RULE__plus__` (y `__RULE__plus__` z)) = (w `__RULE__plus__` x) `__RULE__plus__` (y `__RULE__plus__` z)
  ;
  "multiplicative associativity" ∀ w x y z. w `__RULE__times__` (x `__RULE__times__` (y `__RULE__times__` z)) = (w `__RULE__times__` x) `__RULE__times__` (y `__RULE__times__` z)
  ;
  "left zero anihilation" ∀ x. __RULE__zero__ `__RULE__times__` x = __RULE__zero__
  ;
  "right zero anihilation" ∀ x. x `__RULE__times__` __RULE__zero__ = __RULE__zero__
  ;
  "left zero identity" ∀ x. __RULE__zero__ `__RULE__plus__` x = x
  ;
  "right zero identity" ∀ x. x `__RULE__plus__` __RULE__zero__ = x
  #-}
