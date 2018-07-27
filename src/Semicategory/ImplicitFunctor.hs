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
  FunctionalDependencies
  ,
  MultiParamTypeClasses
  ,
  RankNTypes
  ,
  ConstraintKinds
  ,
  GADTs
  #-}

module Semicategory.ImplicitFunctor
  where

import Semicategory.ImplicitCategory
import Semicategory.ImplicitSemimonoidal
-- import Category.Flip
-- import Data.Kind (Type)
import Prelude (Either(..))

class (Category (d :: Arrow1 i), Category (c :: Arrow1 j)) ⇒ Functor d c (f :: i → j) | d f → c where
  fmap :: d x y → c (f x) (f y)

--- Natural Transformations ---
newtype NT (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j) (g :: i → j) = NT { runNT :: ∀ x. c (f x) (g x) }

instance (Category d, Category c) ⇒ Semicategory (NT d c) where
  type Object (NT d c) = Functor d c
  NT t <<< NT s = NT (t <<< s)

instance (Category d, Category c) ⇒ Category (NT d c) where
  id = NT id

instance
  (Category d, Category c) ⇒
  Functor (Flip (NT d c)) (NT (NT d c) (→)) (NT d c)
  where fmap (Flip t) = NT (t >>>)

instance (Category d, Category c) ⇒ Functor (NT d c) (→) (NT d c f) where
  fmap = (<<<)

type Bifunctor d1 d2 c b = (Functor d1 (NT d2 c) b)

bimap ::
  ∀ d1 d2 c b x x' y y'.
  (Bifunctor d1 d2 c b, Functor d2 c (b x)) ⇒
  d1 x x' → d2 y y' → c (b x y) (b x' y')
bimap f g = runNT (fmap f) <<< fmap g

type Profunctor d c p = (Bifunctor (Opposite d) d c p)

dimap ::
  ∀ d c p x x' y y'.
  (Profunctor d c p, Functor d c (p x)) ⇒
  d x' x → d y y' → c (p x y) (p x' y')
dimap f g = bimap (opposite f) g

instance (Category c, Flip c ~ Opposite c) => Functor c (NT (Flip c) (→)) (Flip c) where
  fmap t = NT (opposite t >>>)

instance (Category c, Flip c ~ Opposite c) => Functor (Flip c) (→) (Flip c k) where
  fmap = (<<<)

instance Functor (Flip (→)) (NT (→) (→)) (→) where
  fmap g = NT (opposite g >>>)

instance Functor (→) (→) ((→) k) where
  fmap = (<<<)

instance Functor (→) (NT (→) (→)) (,) where
  -- fmap f = NT (\(l, k) -> (f l, k))
  fmap f = NT (f <.> id)

instance Functor (→) (→) ((,) k) where
  -- fmap f (k, r) = (k, f r)
  fmap = (id <.>)

instance Functor (→) (NT (→) (→)) Either where
  -- fmap f = NT (\e → case e of
  --                 Left l → Left (f l)
  --                 Right k → Right k)
  fmap f = NT (f <.> id)

instance Functor (→) (→) (Either k) where
  -- fmap _ (Left k) = Left k
  -- fmap f (Right r) = Right (f r)
  fmap = (id <.>)
