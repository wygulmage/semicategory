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
  Semimonoidal(..)
  ,
  Braided(..)
  ,
  Symmetric(..)
  ,
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
  type Unit
  ,
  module Math.Functor.Terminal
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


class Semimonoidal c f ⇒ Braided c f where
  braid :: c (f x y) (f y x)

braidCartesian :: Cartesian c f ⇒ c (f x y) (f y x)
braidCartesian = snd △ fst

braidCocartesian :: Cocartesian c f ⇒ c (f x y) (f y x)
braidCocartesian = inR ▽ inL

class Braided c f ⇒ Symmetric c f where
  swap :: c (f x y) (f y x)
  swap = braid -- swap is an involution.


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


class (Symmetric c f, Semicartesian c f) ⇒ Cartesian c f where
  (△) :: c x l → c x r → c x (f l r)
  infix 4 △

class (Symmetric c f, Semicocartesian c f) ⇒ Cocartesian c f where
  (▽) :: c l x → c r x → c (f l r) x
  infix 4 ▽


----- Instances -----

--- Flipped categories:

instance (Semimonoidal c f, Flip c ~ Opposite c) ⇒ Semimonoidal (Flip c) f where
  assoc = isoFlip assoc

instance (Braided c f, Flip c ~ Opposite c) ⇒ Braided (Flip c) f where
  braid = Flip braid

instance (Symmetric c f, Flip c ~ Opposite c) ⇒ Symmetric (Flip c) f

instance (Monoidal c f, Flip c ~ Opposite c) ⇒ Monoidal (Flip c) f where
  unitL = isoFlip unitL
  unitR = isoFlip unitR

instance (Cartesian c f, Opposite c ~ Flip c) ⇒ Cocartesian (Flip c) f where
  Flip a ▽ Flip b = Flip (a △ b)

instance (Cocartesian c f, Opposite c ~ Flip c) ⇒ Cartesian (Flip c) f where
  Flip a △ Flip b = Flip (a ▽ b)


--- Functions:

--- Cartesian product:

instance Semimonoidal (→) (,) where
  assoc = assocCartesian

instance Braided (→) (,) where
  braid = braidCartesian

instance Symmetric (→) (,)

instance Monoidal (→) (,) where
  unitL = Iso (\(_,x)→x) ((,) ())
  unitR = Iso (\(x,_)→x) (\x→(x,()))

instance Cartesian (→) (,) where
  (a △ b) x = (a x, b x)

--- Disjoint union:

instance Semimonoidal (→) Either where
  assoc = assocCocartesian

instance Braided (→) Either where
  braid = braidCocartesian

instance Symmetric (→) Either

instance Monoidal (→) Either where
  unitL = Iso (\(Right x) → x) Right
  unitR = Iso (\(Left x) → x) Left

instance Cocartesian (→) Either where
  (▽) = either

--- Isomorphisms:

instance
  (Bifunctor (Iso c) (Iso c) (Iso c) f, Semimonoidal c f) ⇒
  Semimonoidal (Iso c) f
  where
  Iso uL rL ⊗ Iso uR rR = Iso (uL ⊗ uR) (rL ⊗ rR)
  assoc = Iso (opposite assoc) assoc

instance
  (Semimonoidal (Iso c) f, Braided c f) ⇒
  Braided (Iso c) f where
  braid = Iso braid braid

instance
  Braided (Iso c) f ⇒ Symmetric (Iso c) f

instance
  (Semimonoidal (Iso c) f, Monoidal c f) ⇒
  Monoidal (Iso c) f where
  unitL = Iso (opposite unitL) unitL
  unitR = Iso (opposite unitR) unitR

instance
  (Ob1 (Iso c) ~ Ob0 (Iso c), Cartesian c f, Cocartesian c f) ⇒
  Cartesian (Iso c) f where
  Iso u1 r1 △ Iso u2 r2 = Iso (u1 ▽ u2) (r1 △ r2)

instance
  (Ob1 (Iso c) ~ Ob0 (Iso c), Cartesian c f, Cocartesian c f) ⇒
  Cocartesian (Iso c) f where
  Iso u1 r1 ▽ Iso u2 r2 = Iso (u1 △ u2) (r1 ▽ r2)


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
