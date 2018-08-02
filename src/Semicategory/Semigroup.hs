{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
  ,
  RankNTypes
  ,
  ExplicitNamespaces
  ,
  ConstraintKinds
  #-}

module Semicategory.Semigroup (
  Semigroup(..)
  ,
  type FreeSemigroup
  ,
  Monoid(..)
  ,
  type Maybe(..)
  ,
  type FreeMonoid
  ,
  type Anihilative(..)
  ,
  type Anihilate(..)
  ,
  type FreeAnihilative
  ,
  LeftCancellative(..)
  ,
  RightCancellative(..)
  ,
  Cancellative
  ,
  Group(..)
  ,
  type FreeGroup
  ) where

-- import Semicategory.Semimonoidal
-- import Semicategory.Closed
import Data.Maybe (Maybe(..))


--- Semigroup ---

class Semigroup s where
  (·) :: s → s → s
  -- Law:
  -- ∀ x y z. (x · y) · z = x · (y · z)

type FreeSemigroup x = ∀ s. Semigroup s ⇒ (x → s) → s

instance Semigroup s ⇒ Semigroup (x → s) where
  -- f · g = curry (·) <<< f &&& x
  (f · g) x = f x · g x

newtype First x = First {getFirst :: x}
instance Semigroup (First x) where s · _ = s

newtype Last x = Last {getLast :: x}
instance Semigroup (Last x) where _ · s = s

instance Semigroup s ⇒ Semigroup (Maybe s) where
  Nothing · m = m
  m · Nothing = m
  Just s · Just t = Just (s · t)

--- Monoid ---

class Semigroup m ⇒ Monoid m where
  identity :: m
  -- Laws:
  -- ∀ x. identity · x = x
  -- ∀ x. x · identity = x

type FreeMonoid x = ∀ m. Monoid m ⇒ (x → m) → m

instance Monoid m ⇒ Monoid (x → m) where
  -- identity = return identity
  identity _ = identity

--- Attach an identity element to a semigroup to create a monoid:
instance Semigroup s ⇒ Monoid (Maybe s) where
  identity = Nothing


--- Anihilative semigroup ---

class Semigroup a ⇒ Anihilative a where
  nihil :: a
  -- Laws:
  -- ∀ x. nihil · x = nihil
  -- ∀ x. x · nihil = nihil

type FreeAnihilative x = ∀ a. Anihilative a ⇒ (x → a) → a

newtype Anihilate x = Anihilate {getAnihilate :: Maybe x}

-- Attach an anihilative element to a semigroup:
instance Semigroup s ⇒ Semigroup (Anihilate s) where
  (Anihilate (Just s)) · (Anihilate (Just t)) = Anihilate (Just (s · t))
  _ · _ = nihil

instance Semigroup s ⇒ Anihilative (Anihilate s) where
  nihil = Anihilate Nothing


--- Cancellative semigroups ---

class Monoid c ⇒ LeftCancellative c where
  undoL :: c → c → c
  undoL x y = y \\ x
  (\\) :: c → c → c
  x \\ y = undoL y x

instance LeftCancellative c ⇒ LeftCancellative (x → c) where
  (f \\ g) x = f x \\ g x

class Monoid c ⇒ RightCancellative c where
  undoR :: c → c → c
  undoR = (//)
  (//) :: c → c → c
  (//) = undoR

instance RightCancellative c ⇒ RightCancellative (x → c) where
  (f // g) x = f x // g x

type Cancellative c = (LeftCancellative c, RightCancellative c)

--- Group ---
class Cancellative g ⇒ Group g where
  negate :: g → g
  negate = (identity //)
  -- Law:
  -- ∀ x y. (x · y) · (neg y) = x

type FreeGroup x = ∀ g. Group g ⇒ (x → g) → g

instance Group g ⇒ Group (x → g) where
  negate f x = negate (f x)
