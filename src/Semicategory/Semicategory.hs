{-# LANGUAGE
  NoImplicitPrelude
  ,
  UnicodeSyntax
  ,
  ExplicitNamespaces
  ,
  TypeInType
  ,
  TypeFamilies
  ,
  MultiParamTypeClasses
  ,
  FlexibleInstances
  ,
  FlexibleContexts
  ,
  DefaultSignatures
  ,
  UndecidableInstances -- CatsObject
  ,
  UndecidableSuperClasses -- CatsObject
  ,
  GADTs
  ,
  TypeOperators
  ,
  Safe
  #-}

module Semicategory.Semicategory (
  type Arrow1
  ,
  Iso(..)
  ,
  Flip(..)
  ,
  flipIso
  ,
  Semicategory(..)
  ,
  EveryObject
  ,
  type Semicats(..)
  ,
  SemicatsObject
  ,
  Pair(..)
  ,
  Fst, Snd
  ) where

import Data.Kind (Type, Constraint)


type Arrow1 o = o → o → Type


data Iso (c :: Arrow1 o) x y = Iso { un :: c y x, run :: c x y }

newtype Flip (c :: i → j → Type) x y = Flip { unFlip :: c y x }


-- type family Opposite (c :: i → j → k) :: j → i → k where
--   Opposite (Iso c) = Iso c
--   Opposite (Flip c) = c
--   Opposite c = Flip c


flipIso :: Flip c ~ Opposite c ⇒ Iso c x y → Iso (Flip c) x y
flipIso (Iso u r) = Iso (Flip r) (Flip u)

class EveryObject o
instance EveryObject o

class Semicategory (c :: Arrow1 o) where
  type Object c :: o → Constraint
  type Object c = EveryObject -- allow everything by default
  type Opposite c :: Arrow1 o
  type Opposite c = Flip c
  opposite :: c x y → Opposite c y x
  default opposite :: Opposite c ~ Flip c ⇒ c x y → Opposite c y x
  opposite = Flip
  (>>>) :: c x y → c y z → c x z
  (<<<) :: c y z → c x y → c x z
  (>>>) f = (<<< f)
  (<<<) f = (>>> f)


instance Semicategory c ⇒ Semicategory (Iso c) where
  type Object (Iso c) = Object c
  type Opposite (Iso c) = Iso c
  opposite (Iso u r) = Iso r u
  Iso u1 r1 >>> Iso u2 r2 = Iso (u1 <<< u2) (r1 >>> r2)


instance (Semicategory c, Flip c ~ Opposite c) ⇒ Semicategory (Flip c) where
  type Object (Flip c) = Object c
  type Opposite (Flip c) = c
  opposite = unFlip
  Flip a >>> Flip b = Flip (a <<< b)


--- Examples ---

instance Semicategory (→) where
  type Object (→) = EveryObject
  (f <<< g) x = f (g x)

instance Semicategory (,) where
  type Object (,) = EveryObject
  type Opposite (,) = (,)
  opposite (l, r) = (r, l)
  (l, _) >>> (_, r) = (l, r)


--- Product Semicategory ---

-- data Semicats (c :: Arrow1 l) (d :: Arrow1 r) (x :: (l, r)) (x' :: (l, r)) where
--   Semicats ::
--     (Semicategory c, Semicategory d) ⇒
--     { getSemicats :: (c (Fst x) (Fst x'), d (Snd x) (Snd x')) } → Semicats c d x x'

newtype Semicats c d x x' = Semicats { getSemicats :: (c (Fst x) (Fst x'), d (Snd x) (Snd x')) }

type family Fst (x :: (l, r)) :: l where Fst '(l, r) = l
type family Snd (x :: (l, r)) :: r where Snd '(l, r) = r

class (Object c (Fst x), Object d (Snd x)) ⇒ SemicatsObject (c :: Arrow1 l) (d :: Arrow1 r) (x :: (l, r))
instance (Object c (Fst x), Object d (Snd x)) ⇒ SemicatsObject (c :: Arrow1 l) (d :: Arrow1 r) (x :: (l, r))
-- Great, but how do you create such an object?

data Pair :: (Type, Type) → Type where
  Pair :: (x, y)  → Pair '(x, y)

pairToFn :: Pair '(x, y) → (x → y → z) → z
pairToFn (Pair (x, y)) f = f x y

-- data UncurriedProduct (p :: i → j → Type) :: (i, j) → Type where
--   ????

-- type family Uncurry (x :: i → j → k) :: (i, j) → k where Uncurry

instance (Semicategory c, Semicategory d) ⇒ Semicategory (Semicats c d) where
  type Object (Semicats c d) = SemicatsObject c d
  type Opposite (Semicats c d) = Semicats (Opposite c) (Opposite d)
  opposite (Semicats (a, b)) = Semicats (opposite a, opposite b)
  Semicats (f, g) >>> Semicats (f', g') = Semicats (f >>> f', g >>> g')

-- data Cats' :: Arrow1 Type → Arrow1 Type → Arrow1 Type where
--   Cats' :: c x x' → d y y' → Cats' c d (x, y) (x', y')
