{-# Language OverloadedStrings #-}
{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language DeriveGeneric #-}
{-# Language DefaultSignatures #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language KindSignatures #-}
{-# Language ScopedTypeVariables #-}
{-# Language DeriveAnyClass #-}

module Generics.Simple where

import Data.Text
import GHC.Generics
import Data.Proxy
import GHC.TypeLits
import Language.Haskell.TH
import Control.Monad.State.Strict
import qualified Data.Map.Strict as DMS

data CName = CName Text deriving (Show)

data HField_ a = HField (Maybe Text) (HType_ a) deriving (Show)

type HState = State (DMS.Map MData ())

data MData =
  MData
    { _mTypeName :: Text
    , _mModuleName :: Text
    , _mPackageName :: Text
    , _mTypeArgs :: Maybe [Name]
    } deriving (Show, Ord, Eq)

data HConstructor_ a
  = HConstructor CName [HField_ a]
  deriving (Show)

data HType_ a
  = HType MData [HConstructor_ a] a
  | HMaybe MData (HType_ a)
  | HList (HType_ a)
  | HPrimitive MData a
  | HTypeVar Text -- Used when representing polymorphic types
  | HRecursive MData
  deriving (Show)

type HType = HType_ ()
type HField = HField_ ()
type HConstructor = HConstructor_ ()

class ToHType_ (f :: * -> *) where
  toHType_ :: (Proxy f) -> HState HType

class ToHField_ (f :: * -> *) where
  toHField_ :: (Proxy f) -> HState [HField]

class ToHConstructor_ (f :: * -> *) where
  toHConstructor_ :: (Proxy f) -> HState [HConstructor]

class ToHType f where
  toHType :: (Proxy f) -> HState HType
  default toHType :: (Generic f, ToHType_ (Rep f)) => (Proxy f) -> HState HType
  toHType _ = toHType_ (Proxy :: (Proxy (Rep f)))

instance (ToHConstructor_ b, KnownSymbol a1, KnownSymbol a2, KnownSymbol a3) => ToHType_ (D1 ('MetaData a1 a2 a3 a4) b) where
  toHType_ _ = let
    mdata = (MData
      (pack $ symbolVal (Proxy :: Proxy a1))
      (pack $ symbolVal (Proxy :: Proxy a2))
      (pack $ symbolVal (Proxy :: Proxy a3))
      Nothing)
    in do
      seen <- get
      case DMS.lookup mdata seen of
        Just _ -> pure $ HRecursive mdata
        Nothing -> do
          put $ DMS.insert mdata () seen
          cons_ <- (toHConstructor_ (Proxy :: Proxy b))
          pure $
            HType mdata cons_ ()

instance (KnownSymbol cname, ToHField_ s) => ToHConstructor_ (C1 ('MetaCons cname a b) s) where
  toHConstructor_ _ = do
    hfield <- toHField_ (Proxy :: Proxy s)
    pure [HConstructor
      (CName $ pack $ symbolVal (Proxy :: Proxy cname)) $
      hfield]

instance ToHField_ U1 where
  toHField_ _ = pure []

instance (KnownSymbol cname, ToHType_ w) => ToHField_ (S1 ('MetaSel ('Just cname) a b c) w) where
  toHField_ _ = do
    htype <- (toHType_ ( Proxy :: Proxy w))
    pure $ [HField (Just $ pack $ symbolVal (Proxy :: Proxy cname)) htype]

instance (ToHType_ w) => ToHField_ (S1 ('MetaSel 'Nothing a b c) w) where
  toHField_ _ = do
    htype <- (toHType_ ( Proxy :: Proxy w))
    pure $ [HField Nothing htype]

instance (ToHField_ a, ToHField_ b) => ToHField_ (a :*: b)where
  toHField_ _ = do
    hfield1 <- (toHField_ (Proxy :: Proxy a))
    hfield2 <-(toHField_ (Proxy :: Proxy b))
    pure $ hfield1 ++ hfield2

instance (ToHConstructor_ a, ToHConstructor_ b) => ToHConstructor_ (a :+: b) where
  toHConstructor_ _ = do
    lhs <- toHConstructor_ (Proxy :: Proxy a)
    rhs <- toHConstructor_ (Proxy :: Proxy b)
    pure $ lhs ++ rhs

instance (ToHType a) => ToHType_ (K1 R a) where
  toHType_ _ = toHType (Proxy :: Proxy a)
