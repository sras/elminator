{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Elminator (module Elminator, ElmVersion(..), HType, ToHType, Builder, GenOption(..), PolyConfig(..)) where

import Elminator.Generics.Simple
import Data.Text as T
import Data.Proxy
import Language.Haskell.TH
import Elminator.Lib
import qualified Elminator.Elm19 as Elm19
import qualified Data.Map.Strict as DMS
import Control.Monad.State.Lazy
import qualified Control.Monad.State.Strict as SState
import Control.Monad.Reader
import Data.Aeson (Options)

-- Primitive instances


instance ToHType Char where
  toHType _ = pure $ HPrimitive (MData "Char" "" "")

instance ToHType Int where
  toHType _ = pure $ HPrimitive (MData "Int" "" "")

instance ToHType Float where
  toHType _ = pure $ HPrimitive (MData "Float" "" "")

instance ToHType Bool where
  toHType _ = pure $ HPrimitive (MData "Bool" "" "")

-- Common types

instance (ToHType a, ToHType b) => ToHType (Either a b)

instance (ToHType a) => ToHType (Maybe a) where
  toHType _ = do
    htype <- (toHType (Proxy :: Proxy a))
    pure $ HMaybe htype

instance (ToHType a, ToHType b) => ToHType (a, b)

instance ToHType ()

instance (ToHType a) => ToHType [a] where
  toHType _ = do
    htype <- (toHType (Proxy :: Proxy a))
    pure $ case htype  of
      HPrimitive (MData "Char" _ _) -> HPrimitive (MData "String" "" "")
      hta -> HList hta

-- | Include the elm source for the Haskell type specified by the proxy argument.
-- The second argument decides which components will be included and if the
-- generated type will be polymorphic.
include
  :: (ToHType a)
  => Proxy a
  -> GenOption
  -> Builder
include p dc = do
  let hType = SState.evalState (toHType p) (DMS.empty)
  mdata <- case hType of
    HUDef (UDefData m _ _ _) -> pure m
    HPrimitive _ -> error "Direct encoding of primitive type is not supported"
    HMaybe _ -> error "Direct encoding of maybe type is not supported"
    HList _ -> error "Direct encoding of list type is not supported"
    HTypeVar _ -> error "Unexpected meta data"
    HRecursive _ -> error "Unexpected meta data"
  s <- get
  put $ DMS.insertWith (++) mdata [(dc, hType)] s

generateFor :: ElmVersion -> Options -> Builder -> Q Exp
generateFor ev opt sc = let
  (_, gc) = runState sc DMS.empty
  r = do
    srcs <- mapM generateOne $ DMS.elems gc
    let
      srcswh = case ev of
        Elm19 -> Elm19.elmFront:srcs
    pure $ toExp $ T.intercalate "" srcswh
  in runReaderT r gc
  where
    toExp :: Text -> Exp
    toExp t = LitE $ StringL $ unpack t
    generateOne :: [(GenOption, HType)] -> LibM Text
    generateOne dcs = do
      srcs <- mapM generateOne_ $ dcs
      pure $ T.intercalate "\n\n" srcs
      where
      generateOne_ :: (GenOption, HType) -> LibM Text
      generateOne_ (d, h) = do
        case ev of
          Elm19 -> Elm19.generateElm d h opt
