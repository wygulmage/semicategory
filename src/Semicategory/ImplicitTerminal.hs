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

module Semicategory.ImplicitTerminal where

import Semicategory.ImplicitSemicategory

import Data.Void (Void, absurd)

class Semicategory c ⇒ Terminal (c :: Arrow1 o) where
  type TerminalObject c :: o
  terminalArrow :: c x (TerminalObject c)


class Semicategory c ⇒ Coterminal (c :: Arrow1 o) where
  type CoterminalObject c :: o
  coterminalArrow :: c (CoterminalObject c) x


instance (Terminal c, Flip c ~ Opposite c) ⇒ Coterminal (Flip c) where
  type CoterminalObject (Flip c) = TerminalObject c
  coterminalArrow = Flip terminalArrow


instance (Coterminal c, Flip c ~ Opposite c) ⇒ Terminal (Flip c) where
  type TerminalObject (Flip c) = CoterminalObject c
  terminalArrow = Flip coterminalArrow


--- Examples ---

instance Terminal (→) where
  type TerminalObject (→) = ()
  terminalArrow _ = ()

instance Coterminal (→) where
  type CoterminalObject (→) = Void
  coterminalArrow = absurd
