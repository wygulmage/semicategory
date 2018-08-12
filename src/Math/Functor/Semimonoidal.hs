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
  UndecidableInstances -- Semimonoidal Iso
  #-}

module Math.Functor.Semimonoidal (
  Semimonoidal(..)
  ,
  module Math.Functor.Functor
  ) where

import Math.Functor.Functor
import Math.Functor.Iso

class Bifunctor c c c f ⇒ Semimonoidal c f where
  (⊗) :: Semimonoidal c f ⇒ c x x' → c y y' → c (f x y) (f x' y')
  (⊗) = bimap
  assoc :: Iso c (f (f x y) z) (f x (f y z))


instance
  (Bifunctor (Iso c) (Iso c) (Iso c) f, Semimonoidal c f) ⇒
  Semimonoidal (Iso c) f
  where
  Iso uL rL ⊗ Iso uR rR = Iso (uL ⊗ uR) (rL ⊗ rR)
  assoc = Iso (opposite assoc) assoc

instance Semimonoidal (→) (,) where
  assoc = Iso
    (\(x, (y, z)) → ((x, y), z))
    (\((x, y), z) → (x, (y, z)))

instance Semimonoidal (→) Either where
  assoc = Iso
    (either (Left ◃ Left) (either (Left ◃ Right) Right)
    (either (either Left (Right ◃ Left)) (Right ◃ Right))

-- type Semimonoidal c f = Bifunctor c c c f
-- (⊗) :: Semimonoidal c f ⇒ c x x' → c y y' → c (f x y) (f x' y')
-- (⊗) = bimap
