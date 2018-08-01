--- Associative Binary Operations---
{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
  ,
  TypeInType
  ,
  ConstraintKinds
  ,
  ConstrainedClassMethods
  ,
  DefaultSignatures
  #-}

module Semicategory.Associative (
  Associative(..)
  ,
  Anihilative(..)
  ,
  HasZero(..)
  ,
  LeftCancellative(..)
  ,
  RightCancellative(..)
  ,
  Cancellative
  ,
  Negatable(..)
  ,
  Distributive(..)
  ,
  HasOne(..)
  ,
  LeftDivisible(..)
  ,
  maybeDivide
  ,
  RightDivisible(..)
  ,
  (/?)
  ,
  Divisible
  ,
  Reciprocated
  ,
  maybeReciprocal
  ,
  Product(..)
  ,
  Lattice(..)
  ,
  HasTop(..)
  ,
  HasBottom(..)
  ,
  Complemented(..)
  ,
  DistributiveLattice
  ,
  Boolean
  ,
  Join(..)
  ,
  Meet(..)
  ,
  First(..)
  ,
  Last(..)
  ) where

import Data.Void (Void, absurd)
import Data.Maybe (Maybe(..))
import Data.Bool (Bool(..))
import Numeric.Natural (Natural)
import Prelude (Integer)
import qualified Prelude (Eq(..))
import qualified Prelude ((+), (*), (-), (&&), (||), min, max, (<=))

if' :: Bool → x → x → x
if' True t _ = t
if' _ _ f = f

class Associative a where
  (+) :: a → a → a
  -- It's traditional to consider this semigroup/semimonoid operation 'multiplication', but for our simple purposes addition makes more sense (e.g. (+) :: [a] → [a] → [a]).


--- More Properties ---

class Associative a ⇒ Anihilative a where
  nihil :: a

class Associative a ⇒ HasZero a where
  zero :: a
  -- Again, it's traditional to consider this monoid element 'unit' or '1', but we're using (+) as the default associative operation.

class HasZero a ⇒ RightCancellative a where
  (-) :: a → a → a
  default (-) :: Negatable a ⇒ a → a → a
  x - y = x + neg y
  -- (-?) :: a → a → Maybe a
  -- default (-?) :: Prelude.Eq a ⇒ a → a → Maybe a
  -- x -? y = if' (dif Prelude.== zero) Nothing (Just dif) where dif = x - y

class HasZero a ⇒ LeftCancellative a where
  subtract :: a → a → a
  default subtract :: Negatable a ⇒ a → a → a
  subtract x y = neg x + y

type Cancellative a = (LeftCancellative a, RightCancellative a)

class Cancellative a ⇒ Negatable a where
  neg :: a → a
  neg a = zero - a


--- Distributive Associative Operations ---

class Associative a ⇒ Distributive a where
  (*) :: a → a → a

class Distributive a ⇒ HasOne a where
  one :: a

class HasOne a ⇒ RightDivisible a where
  (/) :: a → a → a
  default (/) :: Reciprocated a ⇒ a → a → a
  x / y = x * reciprocal y

(/?) :: (RightDivisible a, HasZero a, Prelude.Eq a) ⇒ a → a → Maybe a
x /? y = if' (x Prelude.== zero) Nothing (Just (x / y))

class HasOne a ⇒ LeftDivisible a where
  divide :: a → a → a
  default divide :: Reciprocated a ⇒ a → a → a
  divide x y = reciprocal x * y

maybeDivide :: (Reciprocated a, HasZero a, Prelude.Eq a) ⇒ a → a → Maybe a
maybeDivide x y = if' (y Prelude.== zero) Nothing (Just (divide x y))

type Divisible a = (LeftDivisible a, RightDivisible a)

class Divisible a ⇒ Reciprocated a where
  reciprocal :: a → a
  reciprocal a = one / a

maybeReciprocal :: (Reciprocated a, HasZero a, Prelude.Eq a) ⇒ a → Maybe a
maybeReciprocal a = if' (a Prelude.== zero)
                      Nothing
                      (Just (reciprocal a))

-- The 'Product' newtype transforms distributive multiplication back into an associative operation:
newtype Product a = Product {getProduct :: a}

instance Distributive a ⇒ Associative (Product a) where
  Product x + Product y = Product (x * y)

instance (Distributive a, HasZero a) ⇒ Anihilative (Product a) where
  nihil = Product zero

instance HasOne a ⇒ HasZero (Product a) where
  zero = Product one

instance RightDivisible a ⇒ RightCancellative (Product a) where
  Product x - Product y = Product (x / y)

instance LeftDivisible a ⇒ LeftCancellative (Product a) where
  subtract (Product x) (Product y) = Product (divide x y)

instance Reciprocated a ⇒ Negatable (Product a) where
  neg (Product a) = Product (reciprocal a)



--- Absorptive, Idempotent, Associative Operations ---

class Lattice l where
  (\/), (/\) :: l → l → l

class Lattice l ⇒ HasBottom l where
  bot :: l

class Lattice l ⇒ HasTop l where
  top :: l

type Bounded l = (HasBottom l, HasTop l)

class Bounded l ⇒ Complemented l where
  not :: l → l
-- Laws:
-- ∀ a. a \/ not a = top
-- ∀ a. not a /\ a = bot

class Lattice l ⇒ DistributiveLattice l

type Boolean l = (DistributiveLattice l, Complemented l)

--- 'Join' translates (\/) back into an associative operation. ---
newtype Join l = Join {getJoin :: l}

instance Lattice l ⇒ Associative (Join l) where
  Join x + Join y = Join (x \/ y)

instance HasBottom l ⇒ HasZero (Join l) where
  zero = Join bot

instance HasTop l ⇒ Anihilative (Join l) where
  nihil = Join top

--- 'Meet' translates (\/) back into an associative operation. ---
newtype Meet l = Meet {getMeet :: l}

instance Lattice l ⇒ Associative (Meet l) where
  Meet x + Meet y = Meet (x \/ y)

instance HasTop l ⇒ HasZero (Meet l) where
  zero = Meet top

instance HasBottom l ⇒ Anihilative (Meet l) where
  nihil = Meet bot

--- In distributive lattices, (/\) and (\/) mutually distribute over each other.
instance DistributiveLattice l ⇒ Distributive (Meet l) where
  Meet x * Meet y = Meet (x \/ y)

instance (DistributiveLattice l, HasBottom l) ⇒ HasOne (Meet l) where
  one = Meet bot

instance DistributiveLattice l ⇒ Distributive (Join l) where
  Join x * Join y = Join (x /\ y)

instance (DistributiveLattice l, HasTop l) ⇒ HasOne (Join l) where
  one = Join top

----- Examples -----

--- Functions ---

instance Associative a ⇒ Associative (x → a) where
  (f + g) x = f x + g x

instance Anihilative a ⇒ Anihilative (x → a) where
  nihil _ = nihil

instance HasZero a ⇒ HasZero (x → a) where
  zero _ = zero

instance LeftCancellative a ⇒ LeftCancellative (x → a) where
  subtract f g x = subtract (f x) (g x)

instance RightCancellative a ⇒ RightCancellative (x → a) where
  (f - g) x = f x - g x

instance Negatable a ⇒ Negatable (x → a) where
  neg f x = neg (f x)

instance Distributive a ⇒ Distributive (x → a) where
  (f * g) x = f x * g x

instance HasOne a ⇒ HasOne (x → a) where
  one _ = one

instance LeftDivisible a ⇒ LeftDivisible (x → a) where
  divide f g x = divide (f x) (g x)

instance RightDivisible a ⇒ RightDivisible (x → a) where
  (f / g) x = f x / g x

instance Reciprocated a ⇒ Reciprocated (x → a) where
  reciprocal f x = reciprocal (f x)


--- Trivial Associative Operations ---

instance Associative Void where (+) = absurd

instance Associative () where _ + _ = ()
instance Anihilative () where nihil = ()
instance HasZero () where zero = ()
instance LeftCancellative ()
instance RightCancellative ()
instance Negatable () where neg _ = ()

newtype First x = First {getFirst :: x}

instance Associative (First x) where
  a + _ = a

newtype Last x = Last {getLast :: x}

instance Associative (Last x) where
  _ + a = a

--- Maybe: Attach a Zero ---

instance Associative a ⇒ Associative (Maybe a) where
  Just x + Just y = Just (x + y)
  Nothing + m = m
  m + Nothing = m

instance Associative a ⇒ HasZero (Maybe a) where
  zero = Nothing

--- Pair ---

instance (Associative l, Associative r) ⇒ Associative (l, r) where
  (w, x) + (y, z) = (w + y, x + z)

instance (HasZero l, HasZero r) ⇒ HasZero (l, r) where
  zero = (zero, zero)

instance (Anihilative l, Anihilative r) ⇒ Anihilative (l, r) where
  nihil = (nihil, nihil)

instance (RightCancellative l, RightCancellative r) ⇒ RightCancellative (l, r) where
  (w, x) - (y, z) = (w - y, x - z)

-- etc.

--- Bool: Distributive Lattice ---

instance Lattice Bool where
  (\/) = (Prelude.||)
  (/\) = (Prelude.&&)

instance HasBottom Bool where bot = False

instance HasTop Bool where top = True

instance Complemented Bool where
  not True = False
  not _ = True

instance DistributiveLattice Bool
instance Associative Bool where (+) = (\/)
instance Anihilative Bool where nihil = top
instance HasZero Bool where zero = bot
instance Distributive Bool where (*) = (/\)
instance HasOne Bool where one = top


--- Natural Numbers ---

instance Associative Natural where
  (+) = (Prelude.+)

instance HasZero Natural where zero = 0

instance RightCancellative Natural where
  (-) = (Prelude.-)

instance LeftCancellative Natural where
  subtract x y = y - x

instance Distributive Natural where
  (*) = (Prelude.*)

instance HasOne Natural where one = 1

instance Lattice Natural where
  (\/) = Prelude.max
  (/\) = Prelude.min

instance HasBottom Natural where bot = zero


--- Integers ---

instance Associative Integer where
  (+) = (Prelude.+)

instance HasZero Integer where zero = 0

instance RightCancellative Integer where
  (-) = (Prelude.-)

instance LeftCancellative Integer where
  subtract x y = y - x

instance Negatable Integer where
  neg x = -x

instance Distributive Integer where
  (*) = (Prelude.*)

instance HasOne Integer where
  one = 1

instance Lattice Integer where
  (\/) = Prelude.max
  (/\) = Prelude.min
