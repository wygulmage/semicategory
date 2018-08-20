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
  RankNTypes
  ,
  ScopedTypeVariables
  ,
  MultiParamTypeClasses
  ,
  FlexibleContexts
  ,
  FlexibleInstances
  ,
  UndecidableSuperClasses
  ,
  FunctionalDependencies
  #-}

module Math.Functor.Adjoint where

import Math.Functor.Functor
import Math.Functor.Iso

class
  (Functor c d l, Functor d c r) ⇒
  Adjoint d c l r
  | c l → r, d r → l, d l r → c, c l r → d
  where
  -- adjunctL :: c x (r y) → d (l x) y
  -- adjunctR :: d (l x) y → c x (r y)
  adjunct :: Iso (→) (d (l x) y) (c x (r y))
  inAdjunct :: c x (r (l x)) -- co-evaluation map / unit?
  outAdjunct :: d (l (r y)) y -- evaluation map / co-unit?

type Adj d c l r = ∀ x y. Iso (→) (d (l x) y) (c x (r y))


instance Adjoint (→) (→) ((,) k) ((→) k) where
  adjunct = Iso left right where
    left :: (x → k → y) → (k, x) → y
    left f (k, x) = f x k
    right :: ((k, x) → y) → x → k → y
    right f x k = f (k, x)
  -- inAdjunct :: x → k → (k, x)
  inAdjunct x k = (k, x)
  -- outAdjunct :: (k, (k → y)) → y
  outAdjunct (k, f) = f k

instance (Adjoint d c l r, Opposite c ~ Flip c, Opposite d ~ Flip d) ⇒ Adjoint (Flip c) (Flip d) r l where
  adjunct = Iso left right where
    left (Flip u) = Flip (run adjunct u)
    right (Flip r) = Flip (un adjunct r)
  inAdjunct = Flip outAdjunct
  outAdjunct = Flip inAdjunct
