{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
  ,
  TypeInType
  ,
  TypeFamilies
  ,
  ConstraintKinds
  ,
  MultiParamTypeClasses
  ,
  FlexibleContexts
  ,
  FlexibleInstances
  ,
  UndecidableSuperClasses
  ,
  UndecidableInstances -- for Flip'd Monoidal categories
  #-}

module Math.Functor.Monoidal (
  Monoidal(..)
  ,
  Semicartesian, fst, snd
  ,
  Semicocartesian, inL, inR
  ,
  Cartesian(..)
  ,
  Cocartesian(..)
  ,
  module Math.Functor.Semimonoidal
  ,
  type Unit
  ,
  module Math.Functor.Iso
  ) where

import Math.Functor.Terminal
import Math.Functor.Unit
import Math.Functor.Iso
import Data.Either (Either(..), either)


class Bifunctor c c c f ⇒ Semimonoidal c f where
  (⊗) :: Semimonoidal c f ⇒ c x x' → c y y' → c (f x y) (f x' y')
  (⊗) = bimap
  assoc :: Iso c (f (f x y) z) (f x (f y z))

assocCartesian :: Cartesian c f ⇒ Iso c (f (f x y) z) (f x (f y z))
assocCartesian = Iso
  ((fst △ fst ◃ snd) △ snd ◃ snd)
  (fst ◃ fst △ (snd ◃ fst △ snd))

assocCocartesian :: Cocartesian c f ⇒ Iso c (f (f x y) z) (f x (f y z))
assocCocartesian = Iso
  (inL ◃ inL ▽ (inL ◃ inR ▽ inR))
  ((inL ▽ inR ◃ inL) ▽ inR ◃ inR)

instance
  (Bifunctor (Iso c) (Iso c) (Iso c) f, Semimonoidal c f) ⇒
  Semimonoidal (Iso c) f
  where
  Iso uL rL ⊗ Iso uR rR = Iso (uL ⊗ uR) (rL ⊗ rR)
  assoc = Iso (opposite assoc) assoc

instance Semimonoidal (→) (,) where
  assoc = assocCartesian

instance Semimonoidal (→) Either where
  assoc = assocCocartesian

class Semimonoidal c f ⇒ Monoidal c f where
  unitL :: Iso c x (f (Unit f) x)
  unitR :: Iso c x (f x (Unit f))


type Semicartesian c f = (Monoidal c f, Terminal c, Unit f ~ Ob1 c)

fst :: Semicartesian c f ⇒ c (f x k) x
fst = un unitR ◃ (idS ⊗ arrow1)

snd :: Semicartesian c f ⇒ c (f k x) x
snd = un unitL ◃ (arrow1 ⊗ idS)


type Semicocartesian c f = (Monoidal c f, Coterminal c, Unit f ~ Ob0 c)

inL :: Semicocartesian c f ⇒ c x (f x k)
inL = (idT ⊗ arrow0) ◃ run unitR

inR :: Semicocartesian c f ⇒ c x (f k x)
inR = (arrow0 ⊗ idT) ◃ run unitL


class Semicartesian c f ⇒ Cartesian c f where
  (△) :: c x l → c x r → c x (f l r)
  infix 4 △

class Semicocartesian c f ⇒ Cocartesian c f where
  (▽) :: c l x → c r x → c (f l r) x
  infix 4 ▽


----- Instances -----

--- Flipped categories:

instance (Bifunctor (Flip c) (Flip c) (Flip c) f, Monoidal c f) ⇒ Monoidal (Flip c) f where
  unitL = isoFlip unitL
  unitR = isoFlip unitR
  -- assoc = isoFlip assoc

instance (Cartesian c f, Opposite c ~ Flip c) ⇒ Cocartesian (Flip c) f where
  Flip a ▽ Flip b = Flip (a △ b)

instance (Cocartesian c f, Opposite c ~ Flip c) ⇒ Cartesian (Flip c) f where
  Flip a △ Flip b = Flip (a ▽ b)


--- Functions:

instance Monoidal (→) (,) where
  unitL = Iso (\(_,x)→x) ((,) ())
  unitR = Iso (\(x,_)→x) (\x→(x,()))

instance Monoidal (→) Either where
  unitL = Iso (\(Right x) → x) Right
  unitR = Iso (\(Left x) → x) Left

instance Cartesian (→) (,) where
  (a △ b) x = (a x, b x)

instance Cocartesian (→) Either where
  (▽) = either



--- Semicartesian and Semicocartesian as classes:

-- class (Monoidal c f, Terminal c, Unit f ~ Ob1 c) ⇒ Semicartesian c f where
--   fst :: c (f x k) x
--   snd :: c (f k x) x
--   fst = un unitR ◃ (idS ⊗ arrow1)
--   snd = un unitL ◃ (arrow1 ⊗ idS)

-- instance (Monoidal c f, Terminal c, Unit f ~ Ob1 c) ⇒ Semicartesian c f

-- class (Monoidal c f, Coterminal c, Unit f ~ Ob0 c) ⇒ Semicocartesian c f where
--   inL :: c x (f x k)
--   inR :: c x (f k x)
--   inL = (idT ⊗ arrow0) ◃ run unitR
--   inR = (arrow0 ⊗ idT) ◃ run unitL

-- instance (Monoidal c f, Coterminal c, Unit f ~ Ob0 c) ⇒ Semicocartesian c f
