{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE EmptyDataDecls         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE GADTs                  #-}

module HarmTrace.Base.GenericRep where

import Language.Haskell.TH.Syntax (Name)

import HarmTrace.HAnTree.Tree (Tree)
import HarmTrace.HAnTree.HAn (HAn)

import HarmTrace.HAnTree.Tree (Tree)
import HarmTrace.HAnTree.HAn (HAn)
import Text.ParserCombinators.UU
import Text.ParserCombinators.UU.BasicInstances

infixr 5 :+:
infixr 6 :*:

-- Sums for alternatives (constructors)
data a :+: b = L a | R b

-- Products for arguments to a constructor
data a :*: b = a :*: b

-- Constructor tag
data C c a = C a

-- Unit type for constructors with no arguments
data U = U

-- Variable tag for type parameters
data Var a = Var a

-- Recursive tag for recursive occurrences of the datatype
data Rec a = Rec a

-- The Representable class
class Representable a where
  type Rep a
  to   :: Rep a -> a
  from :: a -> Rep a

-- Constructor meta-information (simplified for now)
class Constructor c where
  conName :: c -> String
  -- conFixity :: c -> Fixity -- Add if needed

-- The "real" GTree class that users will instance
class GTree a where
  gTree :: a -> [Tree HAn]

-- Generic GTree class
class GTree' a where
  gTree' :: a -> [Tree HAn]

-- Default implementation for GTree
gTreeDefault :: (Representable a, GTree' (Rep a)) => a -> [Tree HAn]
gTreeDefault x = gTree' (from x)

-- Instances for GTree'
instance GTree' U where
  gTree' _ = []

instance (GTree' a, GTree' b) => GTree' (a :+: b) where
  gTree' (L x) = gTree' x
  gTree' (R x) = gTree' x

instance (GTree' a, GTree' b) => GTree' (a :*: b) where
  gTree' (x :*: y) = gTree' x ++ gTree' y

instance (GTree a) => GTree' (Var a) where
  gTree' (Var x) = gTree x

instance (GTree a) => GTree' (Rec a) where
  gTree' (Rec x) = gTree x

instance (GTree' a) => GTree' (C c a) where
  gTree' (C x) = gTree' x

-- The "real" ParseG class that users will instance
class ParseG a where
  parseG :: P (Str Char String LineCol) a

-- Generic ParseG class
class ParseG' a where
  parseG' :: P (Str Char String LineCol) a

-- Default implementation for ParseG
parseGdefault :: (Representable a, ParseG' (Rep a)) => P (Str Char String LineCol) a
parseGdefault = to <$> parseG'

-- Instances for ParseG'
instance ParseG' U where
  parseG' = pReturn U

instance (ParseG' a, ParseG' b) => ParseG' (a :+: b) where
  parseG' = (L <$> parseG') <|> (R <$> parseG')

instance (ParseG' a, ParseG' b) => ParseG' (a :*: b) where
  parseG' = (:*:) <$> parseG' <*> parseG'

instance (ParseG a) => ParseG' (Var a) where
  parseG' = Var <$> parseG

instance (ParseG a) => ParseG' (Rec a) where
  parseG' = Rec <$> parseG

instance (Constructor c, ParseG' a) => ParseG' (C c a) where
  parseG' = C <$> parseG'
