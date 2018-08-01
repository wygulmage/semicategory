{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
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
  ,
  RankNTypes
  ,
  FunctionalDependencies
  ,
  InstanceSigs
  ,
  ConstraintKinds
 #-}

module Math.Semimonoidal
  where

import Math.Semicategory
import Math.Terminal
import Data.Either (Either(..))
-- import Data.Void (Void)

{-
Cartesian (Braided, Semicartesian)
Cocartesian (Braided, Semicocartesian)
Semicartesian ⇔ Monoidal, Terminal, monoidal unit = terminal object
Semicocartesian ⇔ Monoidal, Coterminal, monoidal unit = coterminal object
Braided (Premonoidal)
Monoidal
Premonoidal
-}

-- |The unit of the monoidal product is factored out to make the flipped instances easier to define.
type family Unit (p :: o → o → o) :: o -- unit of a monoidal product
type instance Unit (,) = ()
type instance Unit Either = Void

flipIso :: Iso c x y → Iso (Flip c) x y
flipIso (Iso u r) = Iso (Flip r) (Flip u)

class Semicategory c ⇒ Semimonoidal (c :: Arrow1 i) (p :: i → i → i) where
  (⊙) :: c l l' → c r r' → c (p l r) (p l' r')
  assoc :: Iso c (p l (p m r)) (p (p l m) r)

instance (Semimonoidal c p, Flip c ~ Opposite c) ⇒ Semimonoidal (Flip c) p where
  Flip f ⊙ Flip g = Flip (f ⊙ g)
  assoc = flipIso assoc

instance Semimonoidal c p ⇒ Semimonoidal (Iso c) p where
  Iso u1 r1 ⊙ Iso u2 r2 = Iso (u1 ⊙ u2) (r1 ⊙ r2)
  assoc = assoc

class Semimonoidal c p ⇒ Monoidal c p where
  unitL :: Iso c r (p (Unit p) r)
  unitR :: Iso c l (p l (Unit p))

instance (Monoidal c p, Flip c ~ Opposite c) ⇒ Monoidal (Flip c) p where
  unitL = flipIso unitL
  unitR = flipIso unitR

instance Monoidal c p ⇒ Monoidal (Iso c) p where
  unitL = unitL
  unitR = unitR

class Semimonoidal c p ⇒ Braided c p where
  braid :: c (p x y) (p y x)

instance (Braided c p, Flip c ~ Opposite c) ⇒ Braided (Flip c) p where
  braid = Flip braid

instance Braided c p ⇒ Braided (Iso c) p where
  braid = Iso braid braid

-- As a sacrifice to the god of efficiency, Semicartesian and Semicocartesian have to be declared even though they are fully determined by their superclasses.
class (Monoidal c p, Terminal c, Unit p ~ TerminalObject c) ⇒ Semicartesian c p where
  fst :: c (p l r) l
  snd :: c (p l r) r
  default fst :: Category c ⇒ c (p l r) l
  default snd :: Category c ⇒ c (p l r) r
  fst = un unitR ◃ (idS ⊙ terminalArrow)
  snd = un unitL ◃ (terminalArrow ⊙ idS)

class (Monoidal c p, Coterminal c, Unit p ~ CoterminalObject c) ⇒ Semicocartesian c p where
  inL :: c l (p l r)
  inR :: c r (p l r)
  default inL :: Category c ⇒ c l (p l r)
  default inR :: Category c ⇒ c r (p l r)
  inL = run unitR ▹ (idT ⊙ coterminalArrow)
  inR = run unitL ▹ (coterminalArrow ⊙ idT)

instance (Semicartesian c p, Flip c ~ Opposite c) ⇒ Semicocartesian (Flip c) p where
  inL = Flip fst
  inR = Flip snd

instance (Semicocartesian c p, Flip c ~ Opposite c) ⇒ Semicartesian (Flip c) p where
  fst = Flip inL
  snd = Flip inR


class Semicartesian c p ⇒ Cartesian c p where
  (△) :: c x l -> c x r -> c x (p l r)

class Semicocartesian c p ⇒ Cocartesian c p where
  (▽) :: c l x -> c r x -> c (p l r) x

instance (Cartesian c p, Flip c ~ Opposite c) ⇒ Cocartesian (Flip c) p where
  Flip f ▽ Flip g = Flip (f △ g)

instance (Cocartesian c p, Flip c ~ Opposite c) ⇒ Cartesian (Flip c) p where
  Flip f △ Flip g = Flip (f ▽ g)


--- Examples ---

instance Cartesian (→) (,) where
  (f △ g) x = (f x, g x)

instance Semicartesian (→) (,) where
  fst (l, _) = l
  snd (_, r) = r

instance Monoidal (→) (,) where
  unitL = Iso snd (terminalArrow △ idS)
  unitR = Iso fst (idS △ terminalArrow)

instance Semimonoidal (→) (,) where
  f ⊙ g = (fst ▹ f) △ (g ◃ snd)
  assoc = Iso
    ((fst ▹ fst) △ ((fst ▹ snd) △ snd))
    ((fst △ (fst ◃ snd)) △ (snd ◃ snd))

instance Cocartesian (→) Either where
  (f ▽ _) (Left l) = f l
  (_ ▽ g) (Right r) = g r

instance Semicocartesian (→) Either where
  inL = Left
  inR = Right

instance Monoidal (→) Either where
  unitL = Iso (coterminalArrow ▽ idT) inR
  unitR = Iso (idT ▽ coterminalArrow) inL

instance Semimonoidal (→) Either where
  f ⊙ g = (inL ◃ f) ▽ (g ▹ inR)
  assoc = Iso
    ((inL ▽ (inL ▹ inR)) ▽ (inR ▹ inR))
    ((inL ◃ inL) ▽ ((inL ◃ inR) ▽ inR))
