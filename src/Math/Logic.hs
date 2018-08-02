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

module Math.Logic (
  type Logic
  ,
  Preorder(..)
  ,
  PartialOrder
  ,
  Equivalence(..)
  ,
  Lattice(..)
  ,
  Meet(..)
  ,
  Join(..)
  ) where

import Math.Semigroup

import Data.Kind (Type)

import Data.Bool (Bool)
import Numeric.Natural (Natural)
import Prelude (Integer)
import Data.Int (Int)

import Data.Char (Char)

import Data.Either (Either)
import Data.Maybe (Maybe)

import qualified Prelude ((<=), (==))


--- Logic ---
type family Logic l :: Type


type instance Logic (x → l) = x → Logic l

type instance Logic Bool = Bool
type instance Logic Natural = Bool
type instance Logic Integer = Bool
type instance Logic Int = Bool

type instance Logic Char = Bool

type instance Logic [l] = Logic l
type instance Logic (Maybe l) = Logic l

type instance Logic (l, r) = Bool
type instance Logic (l, r) = Bool
type instance Logic (Either l r) = Bool


--- Preorder ---
class Preorder p where
  (≤) :: p → p → Logic p
-- Laws:
-- ∀ x. x ≤ x
-- ∀ x y z. x ≤ y ∧ y ≤ z ⇒ x ≤ z

instance Preorder p ⇒ Preorder (x → p) where
  (f ≤ g) x = f x ≤ g x

instance Preorder Bool where
  (≤) = (Prelude.<=)

instance Preorder Natural where
  (≤) = (Prelude.<=)

instance Preorder Integer where
  (≤) = (Prelude.<=)

instance Preorder Int where
  (≤) = (Prelude.<=)

--- Partial Order ---
class Preorder p ⇒ PartialOrder p
-- Laws:
-- ∀ x y. x ≤ y ∧ y ≤ x = x ≡ y

class PartialOrder l ⇒ Lattice l where
  (∧), (∨) :: l → l → l

-- Laws:
-- ∀ x y. x ∨ (y ∧ x) = x
-- ∀ x y. (x ∨ y) ∧ x = x

class Lattice l ⇒ LowerBounded l where
  bot :: l

class Lattice l ⇒ UpperBounded l where
  top :: l

newtype Meet o = Meet {getMeet :: o}

instance Lattice l ⇒ Semigroup (Meet l) where
  Meet x · Meet y = Meet (x ∧ y)

instance UpperBounded l ⇒ Monoid (Meet l) where
  identity = Meet top

newtype Join o = Join {getJoin :: o}

instance Lattice o ⇒ Semigroup (Join o) where
  Join x · Join y = Join (x ∨ y)

instance LowerBounded l ⇒ Monoid (Join l) where
  identity = Join bot


--- Equivalence ---
class Equivalence e where
  (≡) :: e → e → Logic e

instance Equivalence e ⇒ Equivalence (x → e) where
  (f ≡ g) x = f x ≡ g x

instance Equivalence Bool where
  (≡) = (Prelude.==)

instance Equivalence Natural where
  (≡) = (Prelude.==)

instance Equivalence Integer where
  (≡) = (Prelude.==)

instance Equivalence Int where
  (≡) = (Prelude.==)
