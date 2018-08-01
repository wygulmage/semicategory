{-# LANGUAGE
  NoImplicitPrelude
  ,
  UnicodeSyntax
  ,
  ExplicitNamespaces
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
  GADTs
  ,
  Safe
  #-}

module Semicategory.Terminal (
  Terminal(..)
  ,
  Coterminal(..)
  ,
  idT
  ,
  idS
  ) where

import Semicategory.Semicategory

import Data.Void (Void, absurd)

class Semicategory c ⇒ Terminal (c :: Arrow1 o) where
  type TerminalObject c :: o
  terminalArrow :: c x (TerminalObject c)

-- Reconstruct ∀ x. id x from source and terminal arrow:
idS :: (Category c, Terminal c) ⇒ c x x
idS = source terminalArrow

class Semicategory c ⇒ Coterminal (c :: Arrow1 o) where
  type CoterminalObject c :: o
  coterminalArrow :: c (CoterminalObject c) x

-- Reconstruct ∀ x. id x from target and coterminal arrow:
idT :: (Category c, Coterminal c) ⇒ c x x
idT = target coterminalArrow

----- Examples -----

--- Opposite Categories ---

instance (Terminal c, Flip c ~ Opposite c) ⇒ Coterminal (Flip c) where
  type CoterminalObject (Flip c) = TerminalObject c
  coterminalArrow = Flip terminalArrow

instance (Coterminal c, Flip c ~ Opposite c) ⇒ Terminal (Flip c) where
  type TerminalObject (Flip c) = CoterminalObject c
  terminalArrow = Flip coterminalArrow


--- Functions ---

instance Terminal (→) where
  type TerminalObject (→) = ()
  terminalArrow _ = ()

instance Coterminal (→) where
  type CoterminalObject (→) = Void
  coterminalArrow = absurd
