{-# LANGUAGE
  UnicodeSyntax
  ,
  NoImplicitPrelude
  ,
  TypeInType
  ,
  ScopedTypeVariables
  ,
  TypeFamilies
  ,
  RankNTypes
  ,
  ConstraintKinds
  ,
  TypeOperators
  ,
  MultiParamTypeClasses
  ,
  FlexibleContexts
  ,
  FlexibleInstances
  ,
  DefaultSignatures
  ,
  GADTs
  ,
  UndecidableSuperClasses
  ,
  FunctionalDependencies
  #-}

module Math.Category (
  type Arrow1
  ,
  Flip(..)
  ,
  NT(..)
  ,
  Category(..)
  ,
  Functor(..)
  ,
  type Bifunctor, bimap
  ,
  type Profunctor, dimap
  ) where

import Data.Kind (Type, Constraint)
import Math.Flip (Flip(..))
import Data.Maybe (Maybe(..), maybe)
import Data.Either (Either(..), either)
import qualified Data.List (map)
import Control.Applicative (Const(..))
import Data.Functor.Identity (Identity(..))

-- Note on organization: Because there are a lot of mutual (sometimes circular) dependencies, this can't use a 1-class-per-module approach. Each module should contain only mutually dependent things, plus the occasional type alias or utility function. Given the option, a type's class instances are defined with the type rather than the class. For examples, the Category and Functor instances for Iso are in Math.Functor.Iso. But because Monoidal categories are defined with isomorphisms, the Iso instance of Monoidal is in Math.Functor.Monoidal.
-- With fine-grained class hierarchies, it becomes very important to have nice defaults. But with defaults taken from subclasses, the mutual dependencies multiply…

-- Arrows between objects:
type Arrow1 i = i → i → Type
-- These are arrows between objects: '1-arrows', hence 'Arrow1'. Not to be confused with 'arrow1', the arrow to the terminal object (needs better name?).

-- Natural transformations:
data NT :: ∀ i j. Arrow1 i → Arrow1 j → Arrow1 (i → j) where
  NT ::
    (Functor d c f, Functor d c g) ⇒
    {runNT :: ∀ (x :: i). c (f x) (g x)}
    → NT d c f g

-- Functors:
class
  (Category d, Category c) ⇒
  Functor (d :: Arrow1 i) (c :: Arrow1 j) (f :: i → j)
  -- | f d → c
  where
  fmap :: d x y → c (f x) (f y)

-- Laws:
-- fmap b ◃ fmap a = fmap (b ◃ a)


type Bifunctor d1 d2 c = Functor d1 (NT d2 c)

-- type Trifunctor d1 d2 d3 c = Functor d1 (NT d2 (NT d3 c)) -- &c.

bimap ::
  ∀ d1 d2 c f x x' y y'.
  Bifunctor d1 d2 c f ⇒
  d1 x x' → d2 y y' → c (f x y) (f x' y')
bimap a b = case (fmap :: d1 x x' → NT d2 c (f x) (f x')) a of
  NT fmapped_a → fmap b ◃ fmapped_a


type Profunctor d c = Bifunctor (Opposite d) c (→)

dimap ::
  (Category d,
   Profunctor d c f) ⇒
  d x' x → c y y' → f x y → f x' y'
dimap = bimap ◃ unOpposite


-- Categories:
class
  (Profunctor c c c, -- Composition is a profunctor.
   c ~ Opposite (Opposite c), -- Opposite is an involution.
   Category (Opposite c)) ⇒ -- Every category has an opposite category where the objects are the same but the arrows are reversed.
  Category (c :: Arrow1 i)
  where
  type Opposite c :: Arrow1 i
  opposite :: c x y → Opposite c y x
  source :: c x y → c x x
  target :: c x y → c y y
  (◃) :: c y z → c x y → c x z

  -- defaults:
  type Opposite c = Flip c
  default opposite :: Opposite c ~ Flip c ⇒ c x y → Opposite c y x
  opposite = Flip
  unOpposite :: Opposite c y x → c x y
  default unOpposite :: Opposite c ~ Flip c ⇒  Opposite c y x → c x y
  unOpposite = unFlip
  a ◃ b = runNT ((fmap :: Opposite c x y → NT c (→) (c x) (c y))
                   (opposite b)) a
  -- a ◃ b = dimap

infixl 9 ◃

-- Laws:
-- a ◃ (b ◃ c) = (a ◃ b) ◃ c
-- target a ◃ a = a
-- a ◃ source a = a
-- target (target a) = target a
-- source (target a) = target a
-- source (source a) = source a
-- target (source a) = source a
-- opposite (opposite a) = a -- but note that the second 'opposite' is 'opposite' in the opposite category...
-- unOpposite (opposite a) = a

----- Instances -----


-- natural transformations:

instance Category (NT d c) where
  source = source
  target = target
  NT b ◃ NT a = NT (b ◃ a)

instance Functor (Flip (NT d c)) (NT (NT d c) (→)) (NT d c) where
  fmap (Flip (NT a)) = NT (\(NT b) → NT (b ◃ a))

instance Functor (NT d c) (→) (NT d c f) where
  fmap = (◃)


-- flipped arrows:

instance (Category c, Opposite c ~ Flip c) ⇒ Category (Flip c) where
  type Opposite (Flip c) = c
  source (Flip a) = Flip (target a)
  target (Flip a) = Flip (source a)
  opposite = unFlip
  unOpposite = Flip
  Flip b ◃ Flip a = Flip (a ◃ b)

instance (Category c, Category (Flip c)) ⇒ Functor c (NT (Flip c) (→)) (Flip c) where
  fmap a = NT (◃ Flip a)

instance (Category c, Category (Flip c)) ⇒ Functor (Flip c) (→) (Flip c y) where
  fmap = (◃)

instance
  (Category c, Category (Flip c), Functor c c f) ⇒
  Functor (Flip c) (Flip c) f where
  fmap (Flip a) = Flip (fmap a)

instance
  (Category c, Category (Flip c), Functor c (NT c c) f) ⇒
  Functor (Flip c) (NT (Flip c) (Flip c)) f where
  fmap (Flip a) = case (fmap :: c x x' → NT c c (f x) (f x')) a of
    NT t → NT (Flip t)


-- functions:

instance Category (→) where
  source _ x = x
  target _ y = y
  (g ◃ f) x = g (f x)

instance Functor (Flip (→)) (NT (→) (→)) (→) where
  fmap (Flip a) = NT (◃ a)

instance Functor (→) (→) ((→) x) where
  fmap = (◃)

-- Category of Cartesian pairs:

instance Category (,) where
  source (x, _) = (x, x)
  target (_, y) = (y, y)
  (_, z) ◃ (w, _) = (w, z)

instance Functor (Flip (,)) (NT (,) (→)) (,) where
  fmap (Flip a) = NT (◃ a)

instance Functor (,) (→) ((,) k) where
  fmap = (◃)



--- Instances I'd Rather Not Put Here But Which Would Otherwise Be Orphans ---

instance Functor (→) (→) Identity where
  fmap a = Identity ◃ a ◃ runIdentity

instance Functor (→) (→) Maybe where
  fmap a = maybe Nothing (Just ◃ a)

instance Functor (→) (→) [] where
  fmap = Data.List.map


--- Bifunctors:

instance Functor (→) (NT (→) (→)) Const where
  fmap a = NT (Const ◃ a ◃ getConst)

instance Functor (→) (→) (Const k) where
  fmap _ = Const ◃ getConst

instance Functor (→) (NT (→) (→)) (,) where
  fmap a = NT (\(x, k) → (a x, k))

instance Functor (→) (→) ((,) k) where
  fmap a (k, y) = (k, a y)

instance Functor (→) (NT (→) (→)) Either where
  fmap a = NT (either (Left ◃ a) Right)

instance Functor (→) (→) (Either k) where
  fmap a = either Left (Right ◃ a)
