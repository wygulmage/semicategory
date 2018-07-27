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
  MultiParamTypeClasses
  -- ,
  -- GADTs
  ,
  Safe
  #-}

module Semicategory.ExplicitSemimonoidal (
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

import Semicategory.ExplicitSemicategory
import Semicategory.ExplicitCategory
import Semicategory.ExplicitTerminal

import Data.Either (Either(..), either)
import Data.Void (Void)

type family Unit (p :: o → o → o) :: o

type instance Unit (,) = ()
type instance Unit Either = Void


--- Arrows that can be combined in parallel ---
-- '<.>' is an endo-bifunctor in 'c'.
-- 'assoc' shows that it's associative up to isomorphism.
class Semicategory c ⇒ Semimonoidal (c :: Arrow1 o) (p :: o → o → o) where
  (<.>) ::
    (Object c l, Object c l', Object c r, Object c r', Object c (p l r), Object c (p l' r')) ⇒
    c l l' → c r r' → c (p l r) (p l' r')
  assoc :: Iso c (p (p x y) z) (p x (p y z))


--- Add or remove a 'unit' object from parallel arrows. ---
class Semimonoidal c p ⇒ Monoidal (c :: Arrow1 o) (p :: o → o → o) where
  unitL :: Iso c r (p (Unit p) r)
  unitR :: Iso c l (p l (Unit p))


--- Project out any element ---
class (Monoidal c p, Terminal c, Unit p ~ TerminalObject c) ⇒ Semicartesian c p where
  fst ::
    (Object c (p l r), Object c l) ⇒
    c (p l r) l
  snd ::
    (Object c (p l r), Object c r) ⇒
    c (p l r) r
  default fst ::
    (Category c, Object c (p l r), Object c l, Object c r, Object c (TerminalObject c), Object c (p l (TerminalObject c))) ⇒
    c (p l r) l
  fst = un unitR <<< (id <.> terminalArrow)
  default snd ::
    (Category c, Object c (p l r), Object c l, Object c r, Object c (TerminalObject c), Object c (p (TerminalObject c) r)) ⇒
    c (p l r) r
  snd = un unitL <<< (terminalArrow <.> id)


--- Inject in any element ---
class (Monoidal c p, Coterminal c, Unit p ~ CoterminalObject c) ⇒ Semicocartesian c p where
  inL ::
    (Object c (p l r), Object c l) ⇒
    c l (p l r)
  inR ::
    (Object c (p l r), Object c r) ⇒
    c r (p l r)
  default inL ::
   (Category c, Object c (p l r), Object c l, Object c r, Object c (CoterminalObject c), Object c (p l (CoterminalObject c))) ⇒
    c l (p l r)
  inL = run unitR >>> (id <.> coterminalArrow)
  default inR ::
   (Category c, Object c (p l r), Object c l, Object c r, Object c (CoterminalObject c), Object c (p (CoterminalObject c) r)) ⇒
    c r (p l r)
  inR = run unitL >>> (coterminalArrow <.> id)


--- Has 'all' finite universal products or coproducts ---

class Semicartesian c p ⇒ Cartesian c p where
  (&&&) ::
    (Object c x, Object c l, Object c r, Object c (p l r)) ⇒
    c x l → c x r → c x (p l r)
  infix 4 &&&

class Semicocartesian c p ⇒ Cocartesian c p where
  (|||) ::
    (Object c x, Object c l, Object c r, Object c (p l r)) ⇒
    c l x → c r x → c (p l r) x
  infix 4 |||


----- Examples -----

--- Opposite (Pre-)Category ---

instance (Cocartesian c p, Flip c ~ Opposite c) ⇒ Cartesian (Flip c) p where
  Flip a &&& Flip b = Flip (a ||| b)

instance (Cartesian c p, Flip c ~ Opposite c) ⇒ Cocartesian (Flip c) p where
  Flip a ||| Flip b = Flip (a &&& b)

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
  (f &&& g) x = (f x, g x)

instance Semicartesian (→) (,) where
  fst (l, _) = l
  snd (_, r) = r

instance Monoidal (→) (,) where
  unitL = Iso
    snd
    (terminalArrow &&& id)
  unitR = Iso
    fst
    (id &&& terminalArrow)

instance Semimonoidal (→) (,) where
  f <.> g = fst >>> f &&& g <<< snd
  assoc = Iso
    ((fst &&& fst <<< snd) &&& snd <<< snd)
    (fst >>> fst &&& (fst >>> snd &&& snd))


--- Disjoint Union ---

instance Cocartesian (→) Either where
  (|||) = either

instance Semicocartesian (→) Either where
  inL = Left
  inR = Right

instance Monoidal (→) Either where
  unitL = Iso
    (coterminalArrow ||| id)
    inR
  unitR = Iso
    (id ||| coterminalArrow)
    inL

instance Semimonoidal (→) Either where
  f <.> g = (inL <<< f) ||| (g >>> inR)
  assoc = Iso
    (inL <<< inL ||| (inL <<< inR ||| inR))
    ((inL ||| inL >>> inR) ||| inR >>> inR)
