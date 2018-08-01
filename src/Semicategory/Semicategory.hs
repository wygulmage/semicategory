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
  Category(..)
  ,
  Groupoid(..)
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

flipIso :: Flip c ~ Opposite c ⇒ Iso c x y → Iso (Flip c) x y
flipIso (Iso u r) = Iso (Flip r) (Flip u)

class EveryObject o
instance EveryObject o

class Semicategory (c :: Arrow1 o) where
  type Object c :: o → Constraint
  type Opposite c :: Arrow1 o
  opposite :: c x y → Opposite c y x
  (>>>) :: c x y → c y z → c x z
  (<<<) :: c y z → c x y → c x z
  (>>>) f = (<<< f)
  (<<<) f = (>>> f)
  -- Defaults:
  type Object c = EveryObject -- Allow everything.
  type Opposite c = Flip c
  default opposite :: Opposite c ~ Flip c ⇒ c x y → Opposite c y x
  opposite = Flip

class Semicategory c ⇒ Category (c :: Arrow1 o) where
  source :: c x y → c x x
  target :: c x y → c y y

class Category c ⇒ Groupoid (c :: Arrow1 o) where
  invert :: c x y → c y x
  default invert :: c ~ Opposite c ⇒ c x y → c y x
  invert = opposite -- The opposite groupoid is the same groupoid (possibly with some name changes).


----- Examples -----


--- Isos in a Semicategory: The 'Core' ---

instance Semicategory c ⇒ Groupoid (Iso c)

instance Semicategory c ⇒ Category (Iso c) where
  source (Iso u r) = Iso (u <<< r) (r >>> u)
  target (Iso u r) = Iso (u >>> r) (r <<< u)

instance Semicategory c ⇒ Semicategory (Iso c) where
  type Object (Iso c) = Object c
  type Opposite (Iso c) = Iso c
  opposite (Iso u r) = Iso r u
  Iso u1 r1 >>> Iso u2 r2 = Iso (u1 <<< u2) (r1 >>> r2)


--- Flipped Semicategories and Categories ---

instance (Category c, Flip c ~ Opposite c) ⇒ Category (Flip c) where
  source (Flip a) = Flip (target a)
  target (Flip a) = Flip (source a)

instance (Semicategory c, Flip c ~ Opposite c) ⇒ Semicategory (Flip c) where
  type Object (Flip c) = Object c
  type Opposite (Flip c) = c
  opposite = unFlip
  Flip a >>> Flip b = Flip (a <<< b)

--- Pair Groupoid ---

instance Groupoid (,)

instance Category (,) where
  source (s, _) = (s, s)
  target (_, t) = (t, t)

instance Semicategory (,) where
  type Opposite (,) = (,)
  opposite (l, r) = (r, l)
  (l, _) >>> (_, r) = (l, r)

--- 'Category' of Haskell Functions ---

instance Category (→) where
  source _ s = s
  target _ t = t

instance Semicategory (→) where
  type Object (→) = EveryObject
  (f <<< g) x = f (g x)



--- Product Semicategory ---

-- data Semicats (c :: Arrow1 l) (d :: Arrow1 r) (x :: (l, r)) (x' :: (l, r)) where
--   Semicats ::
--     (Semicategory c, Semicategory d) ⇒
--     { getSemicats :: (c (Fst x) (Fst x'), d (Snd x) (Snd x')) } → Semicats c d x x'

newtype Semicats c d x x' = Semicats { getSemicats :: (c (Fst x) (Fst x'), d (Snd x) (Snd x')) }

type family Fst (x :: (l, r)) :: l where Fst '(l, r) = l
type family Snd (x :: (l, r)) :: r where Snd '(l, r) = r

class
  (Object c (Fst x), Object d (Snd x)) ⇒
  SemicatsObject (c :: Arrow1 l) (d :: Arrow1 r) (x :: (l, r))
instance
  (Object c (Fst x), Object d (Snd x)) ⇒
  SemicatsObject (c :: Arrow1 l) (d :: Arrow1 r) (x :: (l, r))
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
