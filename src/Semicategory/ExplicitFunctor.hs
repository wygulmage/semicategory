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
  FlexibleInstances
  ,
  FlexibleContexts
  ,
  DefaultSignatures
  ,
  InstanceSigs
  ,
  MultiParamTypeClasses
  ,
  RankNTypes
  ,
  ConstraintKinds
  ,
  GADTs
  #-}

module Semicategory.ExplicitFunctor
  where

import Semicategory.ExplicitCategory
-- import Semicategory.Semimonoidal
-- import Category.Flip
-- import Data.Kind (Type)
-- import Prelude (Either(..))

class (Category (d :: Arrow1 i), Category (c :: Arrow1 j)) ⇒ Functor d c (f :: i → j) where
  fmap ::
    (Object d x, Object d y, Object c (f x), Object c (f y)) ⇒
    d x y → c (f x) (f y)

data NT (d :: Arrow1 j) (c :: Arrow1 k) (f :: j → k) (g :: j → k) where
  NT ::
    (Functor d c f, Functor d c g) ⇒
    {runNT ::
        ∀ x. (Object d x, Object c (f x), Object c (g x)) ⇒
        c (f x) (g x)} → NT d c f g

instance (Category d, Category c) ⇒ Semicategory (NT d c) where
  type Object (NT d c) = Functor d c
  NT t <<< NT s = NT (t <<< s)

instance (Category d, Category c) ⇒ Category (NT d c) where
  id = NT (id :: ∀ f x. (Functor d c f) ⇒ c (f x) (f x))

-- instance
--   (Category d, Category c) ⇒
--   Functor (Flip (NT d c)) (NT (NT d c) (→)) (NT d c)
--   where fmap (Flip t) = NT (t >>>)

-- instance (Category d, Category c) ⇒ Functor (NT d c) (→) (NT d c f) where
--   fmap = (<<<)

-- type Copresheaves c = NT c (→)
-- type Presheaves c = Copresheaves (Opposite c)

-- type Endofunctor c f = (Functor c c f)
-- -- type Endobifunctor c f = (Bifunctor )

-- type Bifunctor (d1 :: Arrow1 i) (d2 :: Arrow1 j) (c :: Arrow1 k) (f :: i → j → k) = (Category d1, Category d2, Category c, Functor d1 (NT d2 c) f)

-- bimap :: (Bifunctor (d1 :: Arrow1 i) (d2 :: Arrow1 j) (c :: Arrow1 k) (f :: i → j → k),
--   Functor d1 (NT d2 c) f, Functor d2 c (f x')) ⇒
--   d1 x x' → d2 y y' → c (f x y) (f x' y')
-- -- bimap f g = runNT (fmap f) >>> fmap g
-- bimap f = case fmap f of NT t → t >>> fmap



-- instance (Category c, Flip c ~ Opposite c) => Functor c (NT (Flip c) (→)) (Flip c) where
--   fmap t = NT (opposite t >>>)

-- instance (Category c, Flip c ~ Opposite c) => Functor (Flip c) (→) (Flip c k) where
--   fmap = (<<<)

-- instance Functor (Flip (→)) (Copresheaves (→)) (→) where
--   fmap g = NT (opposite g >>>)

-- instance Functor (→) (→) ((→) k) where
--   fmap = (<<<)

-- instance Functor (→) (Copresheaves (→)) (,) where
--   fmap f = NT (\(l, k) -> (f l, k))

-- instance Functor (→) (→) ((,) k) where
--   fmap = (id <.>)

-- instance Functor (→) (Copresheaves (→)) Either where
--   fmap f = NT (f <.> id)

-- instance Functor (→) (→) (Either l) where
--   fmap = (id <.>)
