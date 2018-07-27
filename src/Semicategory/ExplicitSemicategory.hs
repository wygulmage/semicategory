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
  FlexibleInstances
  ,
  FlexibleContexts
  ,
  DefaultSignatures
  ,
  GADTs
  ,
  Safe
  #-}

module Semicategory.ExplicitSemicategory (
  type Arrow1
  ,
  Iso(..)
  ,
  Flip(..)
  ,
  flipIso
  ,
  type Opposite
  ,
  Semicategory(..)
  ,
  EveryObject
  ) where

import Data.Kind (Type, Constraint)


type Arrow1 o = o → o → Type


-- data Iso c x y = Iso { un :: c y x, run :: c x y }
data Iso (c :: Arrow1 o) x y where
  Iso ::
    Semicategory c ⇒
    { un :: c y x, run :: c x y } → Iso c x y


newtype Flip (c :: i → j → Type) y x = Flip { unFlip :: c x y }


type family Opposite (c :: i → j → k) :: j → i → k where
  Opposite (Iso c) = Iso c
  Opposite (Flip c) = c
  Opposite c = Flip c


flipIso :: Flip c ~ Opposite c ⇒ Iso c x y → Iso (Flip c) x y
flipIso (Iso u r) = Iso (Flip r) (Flip u)

class EveryObject o
instance EveryObject o

class Semicategory (c :: Arrow1 o) where
  type Object c :: o → Constraint
  type Object c = EveryObject -- allow everything by default
  opposite :: c x y → Opposite c y x
  default opposite :: Opposite c ~ Flip c ⇒ c x y → Opposite c y x
  opposite = Flip
  (>>>) ::
    (Object c x, Object c y, Object c z) ⇒
    c x y → c y z → c x z
  (<<<) ::
    (Object c x, Object c y, Object c z) ⇒
    c y z → c x y → c x z
  (>>>) f = (<<< f)
  (<<<) f = (>>> f)


instance Semicategory c ⇒ Semicategory (Iso c) where
  type Object (Iso c) = Object c
  opposite (Iso u r) = Iso r u
  Iso u1 r1 >>> Iso u2 r2 = Iso (u1 <<< u2) (r1 >>> r2)


instance (Semicategory c, Flip c ~ Opposite c) ⇒ Semicategory (Flip c) where
  type Object (Flip c) = Object c
  opposite = unFlip
  Flip a >>> Flip b = Flip (a <<< b)


--- Examples ---

instance Semicategory (→) where
  type Object (→) = EveryObject
  (f <<< g) x = f (g x)

instance Semicategory (,) where
  type Object (,) = EveryObject
  (l, _) >>> (_, r) = (l, r)
