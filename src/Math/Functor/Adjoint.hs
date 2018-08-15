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

class (Functor c d l, Functor d c r) ⇒ Adjoint d c l r where
  -- adjunctL :: c x (r y) → d (l x) y
  -- adjunctR :: d (l x) y → c x (r y)
  adjunct :: Iso (→) (d (l x) y) (c x (r y))

type Adj d c l r = ∀ x y. Iso (→) (d (l x) y) (c x (r y))


instance Adjoint (→) (→) ((,) k) ((→) k) where
  adjunct = Iso left right where
    left :: (x → k → y) → (k, x) → y
    left f (k, x) = f x k
    right :: ((k, x) → y) → x → k → y
    right f x k = f (k, x)
