{-# LANGUAGE
  NoImplicitPrelude
  ,
  UnicodeSyntax
  ,
  ScopedTypeVariables
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
  MultiParamTypeClasses
  -- ,
  -- GADTs
  ,
  Safe
  #-}

module Semicategory.Semimonoidal (
  type Unit
  ,
  type Either(..)
  ,
  type Void
  ,
  Semimonoidal(..)
  ,
  Monoidal(..)
  ,
  Semicartesian(..)
  ,
  Semicocartesian(..)
  ,
  Cartesian(..)
  ,
  Cocartesian(..)
  ) where

import Semicategory.Semicategory
-- import Semicategory.Category
import Semicategory.Terminal

import Data.Either (Either(..), either)
import Data.Void (Void)

type family Unit (p :: o → o → o) :: o

type instance Unit (,) = ()
type instance Unit Either = Void


--- Arrows that can be combined in parallel ---
-- '<.>' is an endo-bifunctor in 'c'.
-- 'assoc' shows that it's associative up to isomorphism.
class Semicategory c ⇒ Semimonoidal (c :: Arrow1 o) (p :: o → o → o) where
  (<.>) :: c l l' → c r r' → c (p l r) (p l' r')
  assoc :: Iso c (p (p x y) z) (p x (p y z))


--- Add or remove a 'unit' object from parallel arrows. ---
class Semimonoidal c p ⇒ Monoidal (c :: Arrow1 o) (p :: o → o → o) where
  unitL :: Iso c r (p (Unit p) r)
  unitR :: Iso c l (p l (Unit p))


--- Project out any element ---
class (Monoidal c p, Terminal c, Unit p ~ TerminalObject c) ⇒ Semicartesian c p where
  fst :: c (p l r) l
  snd :: c (p l r) r
  default fst :: Category c ⇒ c (p l r) l
  fst = un unitR ◃ (idS <.> terminalArrow)
  default snd :: Category c ⇒ c (p l r) r
  snd = un unitL ◃ (terminalArrow <.> idS)


--- Inject in any element ---
class (Monoidal c p, Coterminal c, Unit p ~ CoterminalObject c) ⇒ Semicocartesian c p where
  inL :: c l (p l r)
  inR :: c r (p l r)
  default inL :: Category c ⇒ c l (p l r)
  inL = run unitR ▹ (idT <.> coterminalArrow)
  default inR :: Category c ⇒ c r (p l r)
  inR = run unitL ▹ (coterminalArrow <.> idT)


--- Has 'all' finite universal products or coproducts ---

class Semicartesian c p ⇒ Cartesian c p where
  (△), (&&&) :: c x l → c x r → c x (p l r)
  (△) = (&&&) -- up pointing white triangle suggested by Conal Elliott,
  (&&&) = (△) -- presumably to represent the triangular diagram
  diagonal :: c x (p x x)
  default diagonal :: Category c ⇒ c x (p x x)
  diagonal = idS △ idS

class Semicocartesian c p ⇒ Cocartesian c p where
  (▽), (|||) :: c l x → c r x → c (p l r) x
  (▽) = (|||) -- down pointing white triangle suggested by Conal Elliott,
  (|||) = (▽) -- presumably to represent the triangular diagram
  codiagonal :: c (p x x) x
  default codiagonal :: Category c ⇒ c (p x x) x
  codiagonal = idT ▽ idT


----- Examples -----

--- Opposite (Pre-)Category ---

instance (Cocartesian c p, Flip c ~ Opposite c) ⇒ Cartesian (Flip c) p where
  Flip a △ Flip b = Flip (a ▽ b)
  diagonal = Flip codiagonal

instance (Cartesian c p, Flip c ~ Opposite c) ⇒ Cocartesian (Flip c) p where
  Flip a ▽ Flip b = Flip (a △ b)
  codiagonal = Flip diagonal

instance (Semicocartesian c p, Flip c ~ Opposite c) ⇒ Semicartesian (Flip c) p where
  fst = Flip inL
  snd = Flip inR

instance (Semicartesian c p, Flip c ~ Opposite c) ⇒ Semicocartesian (Flip c) p where
  inL = Flip fst
  inR = Flip snd

instance (Monoidal c p, Flip c ~ Opposite c) ⇒ Monoidal (Flip c) p where
  unitL = flipIso unitL
  unitR = flipIso unitR

instance (Semimonoidal c p, Flip c ~ Opposite c) ⇒ Semimonoidal (Flip c) p where
  Flip a <.> Flip b = Flip (a <.> b)
  assoc = Iso (Flip (run assoc)) (Flip (un assoc))


--- Isomorphisms ---

instance Monoidal c p ⇒ Monoidal (Iso c) p where
  unitL = unitL
  unitR = unitR

instance Semimonoidal c p ⇒ Semimonoidal (Iso c) p where
  Iso ul rl <.> Iso ur rr = Iso (ul <.> ur) (rl <.> rr)
  assoc = assoc


--- Cartesian Product ---

instance Cartesian (→) (,) where
  (f △ g) x = (f x, g x)

instance Semicartesian (→) (,) where
  fst (l, _) = l
  snd (_, r) = r

instance Monoidal (→) (,) where
  unitL = Iso
    snd
    (terminalArrow △ idS)
  unitR = Iso
    fst
    (idS △ terminalArrow)

instance Semimonoidal (→) (,) where
  f <.> g = (fst ▹ f) △ (g ◃ snd)
  assoc = Iso
    (\(x, (y, z)) → ((x, y), z))
    (\((x, y), z) → (x, (y, z)))


--- Disjoint Union ---

instance Cocartesian (→) Either where
  (▽) = either

instance Semicocartesian (→) Either where
  inL = Left
  inR = Right

instance Monoidal (→) Either where
  unitL = Iso
    (coterminalArrow ▽ idT)
    inR
  unitR = Iso
    (idT ▽ coterminalArrow)
    inL

instance Semimonoidal (→) Either where
  f <.> g = (inL ◃ f) ▽ (g ▹ inR)
  assoc = Iso
    ((inL ◃ inL) ▽ ((inL ◃ inR) ▽ inR))
    ((inL ▽ (inL ▹ inR)) ▽ (inR ▹ inR))
