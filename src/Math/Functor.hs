{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
  ,
  ScopedTypeVariables
  ,
  TypeInType
  ,
  TypeFamilies
  ,
  ConstrainedClassMethods
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
  ,
  GADTs
 #-}

module Math.Functor
  where

import Math.Semicategory
import Math.Monoidal

class (Category (d :: Arrow1 i), Category (c :: Arrow1 j)) ⇒
      Functor d c (f :: i → j) where
  fmap :: d x y → c (f x) (f y)

type Copresheaves c = NT c (→)
type Presheaves c = Copresheaves (Opposite c)

presheaves :: (Category c) ⇒ Flip c x y → Copresheaves c (c x) (c y)
presheaves (Flip a) = NT (a ▹)

-- data NT (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j) (g :: i → j) where
--   NT :: (Category d, Category c) ⇒ { runNT :: ∀ x. c (f x) (g x) } → NT d c f g
newtype NT (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j) (g :: i → j) = NT {runNT :: ∀ x. Object d x ⇒ c (f x) (g x)}

instance (Category d, Category c) ⇒ Semicategory (NT d c) where
  type Object (NT d c) = Functor d c
  NT a ▹ NT b = NT (a ▹ b)

instance ∀ d c. (Category d, Category c) ⇒ Category (NT (d :: Arrow1 i) (c :: Arrow1 j)) where
  source :: NT d c f g → NT d c f f
  source = source
  target :: NT d c f g → NT d c g g
  target = target

instance (Category d, Category c) ⇒ Functor (Flip (NT d c)) (NT (NT d c) (→)) (NT d c) where
  fmap = presheaves

instance (Category d, Category c) ⇒ Functor (NT d c) (→) (NT d c f) where
  fmap = (◃)


instance (Category c, Flip c ~ Opposite c) ⇒ Functor c (NT (Flip c) (→)) (Flip c) where
  fmap f = NT (Flip f ▹)

instance (Category c, Flip c ~ Opposite c) ⇒ Functor (Flip c) (→) (Flip c k) where
  fmap = (◃)


----- Examples -----

--- Functions ---

instance Functor (Flip (→)) (NT (→) (→)) (→) where
  fmap = presheaves

instance Functor (→) (→) ((→) k) where
  fmap = (◃)

--- Cartesian Product ---
-- (rather than using the category of pairs)

instance (Category c, Cartesian c (,)) ⇒ Functor c (NT c (→)) (,) where
  fmap a = NT ((fst ▹ a) &&& snd)

instance (Category c, Cartesian c (,)) ⇒ Functor c (→) ((,) k) where
  fmap a = (fst &&& (a ◃ snd))
