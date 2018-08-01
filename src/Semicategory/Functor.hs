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
  ,
  TypeOperators
  #-}

module Semicategory.Functor
  where

import Semicategory.Semicategory
import Semicategory.Semimonoidal
-- import Category.Flip
-- import Data.Kind (Type)
import Data.Either (Either(..))
import System.IO (IO)
-- Stuff I'm too lazy to re-impliment:
import qualified Prelude (fmap)


class
  (Category (d :: Arrow1 i), Category (c :: Arrow1 j)) ⇒
  Functor d c (f :: i → j)
  -- | d f → c
  where
  fmap :: d x y → c (f x) (f y)

--- Natural Transformations ---
newtype NT (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j) (g :: i → j) =
  NT { runNT :: ∀ x. Object d x ⇒ c (f x) (g x) }

instance (Category d, Category c) ⇒ Semicategory (NT d c) where
  type Object (NT d c) = Functor d c
  NT t <<< NT s = NT (t <<< s)

instance (Category d, Category c) ⇒ Category (NT d c) where
  source = source
  target = target

instance
  (Category d, Category c) ⇒
  Functor (Flip (NT d c)) (NT (NT d c) (→)) (NT d c)
  where fmap (Flip t) = NT (t >>>)

instance (Category d, Category c) ⇒ Functor (NT d c) (→) (NT d c f) where
  fmap = (<<<)

--- Bifunctor ---
type Bifunctor d1 d2 c b = (Functor d1 (NT d2 c) b)

bimap ::
  ∀ d1 d2 c b x x' y y'.
  (Bifunctor d1 d2 c b, Functor d2 c (b x), Object d2 y') ⇒
  d1 x x' → d2 y y' → c (b x y) (b x' y')
bimap f g = runNT ((fmap :: d1 x x' → NT d2 c (b x) (b x')) f) <<< fmap g

type Profunctor d c p = (Bifunctor (Opposite d) d c p)

dimap ::
  ∀ d c p x x' y y'.
  (Profunctor d c p, Functor d c (p x), Object d y') ⇒
  d x' x → d y y' → c (p x y) (p x' y')
dimap f g = bimap (opposite f) g

--- Flipped Categories ---
-- The 'Flip' wrapper allows a Functor instance without overlap, unless you start defining other flipped functors.
instance (Category c, Flip c ~ Opposite c) => Functor c (NT (Flip c) (→)) (Flip c) where
  fmap t = NT (opposite t >>>)

instance (Category c, Flip c ~ Opposite c) => Functor (Flip c) (→) (Flip c k) where
  fmap = (<<<)


--- Function endo-profunctor ---

instance Functor (Flip (→)) (NT (→) (→)) (→) where
  fmap g = NT (opposite g >>>)

instance Functor (→) (→) ((→) k) where
  fmap = (<<<)


--- Monoidal Functors ---

--- Pair ---
instance Functor (→) (NT (→) (→)) (,) where
  -- fmap f = NT (\(l, k) -> (f l, k))
  fmap f = NT (f <.> target (snd :: (l, r) → r))
-- instance (Semicartesian c (,)) ⇒ Functor c (NT c (→)) (,) where
--   -- fmap f = NT (\(l, k) -> (f l, k))
--   fmap f = NT (f <.> target (snd :: c (l, r) r))

instance Functor (→) (→) ((,) k) where
  -- fmap f (k, r) = (k, f r)
  fmap = (target (fst :: (l, r) → l) <.>)

--- Either ---
instance Functor (→) (NT (→) (→)) Either where
  -- fmap f = NT (\e → case e of
  --                 Left l → Left (f l)
  --                 Right k → Right k)
  fmap f = NT (f <.> source (inR :: r → Either l r))

instance Functor (→) (→) (Either k) where
  -- fmap _ (Left k) = Left k
  -- fmap f (Right r) = Right (f r)
  fmap = (source (inL :: l → Either l r) <.>)


----- Standard Function Endofunctors -----

instance Functor (→) (→) IO where
  fmap = Prelude.fmap

instance Functor (→) (→) [] where
  fmap = Prelude.fmap

------
-- instance Functor (Semicats (→) (→)) (→) Pair where
--   fmap ::
--     (x~ '(Fst x, Snd x), x' ~ '(Fst x', Snd x')) ⇒
--     Semicats c d x x' → Pair x → Pair x'
--   fmap (Semicats (f, g)) (Pair (l, r)) = (Pair (f l, g r))
