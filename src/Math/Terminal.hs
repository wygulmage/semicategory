{-# LANGUAGE
  NoImplicitPrelude
  ,
  TypeInType
  ,
  TypeFamilies
  #-}

module Math.Terminal (
  Void
  ,
  Terminal(..)
  ,
  Coterminal(..)
  ) where

import Math.Semicategory
import Data.Void (Void, absurd)

-- In a category, if there is a unique arrow from each object to an object o, o is a terminal object.
class Semicategory c => Terminal (c :: Arrow1 o) where
  type TerminalObject c :: o -- a terminal object
  terminalArrow ::
    c x (TerminalObject c) -- a unique arrow from each object in c to the terminal object

-- In a category, if there is a unique arrow to each object from an object o, o is a coterminal (sometimes called 'initial') object.
class Semicategory c => Coterminal (c :: Arrow1 o) where
  type CoterminalObject c :: o -- a coterminal object
  coterminalArrow ::
    c (CoterminalObject c) x -- a unique arrow from the coterminal object to each object in c


--- Opposite Categories ---

-- If a category c has a terminal object o, o is a coterminal object in (Opposite c).
instance (Terminal c, Flip c ~ Opposite c) => Coterminal (Flip c) where
  type CoterminalObject (Flip c) = TerminalObject c
  coterminalArrow = Flip terminalArrow

-- If a category c has a coterminal object o, o is a terminal object in (Opposite c).
instance (Coterminal c, Flip c ~ Opposite c) => Terminal (Flip c) where
  type TerminalObject (Flip c) = CoterminalObject c
  terminalArrow = Flip coterminalArrow


--- Examples ---

instance Terminal (->) where
  type TerminalObject (->) = ()
  terminalArrow _ = ()

instance Coterminal (->) where
  type CoterminalObject (->) = Void
  coterminalArrow = absurd
