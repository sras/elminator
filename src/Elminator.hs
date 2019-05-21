{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

module Elminator
  ( module Elminator
  , ElmVersion(..)
  , HType(..)
  , ToHType(..)
  , ExItem(..)
  , ExInfo(..)
  , Builder
  , GenOption(..)
  , PolyConfig(..)
  ) where

import Control.Monad.Reader
import Control.Monad.State.Lazy
import qualified Control.Monad.State.Strict as SState
import Control.Monad.Writer
import Data.Aeson (Options)
import Data.List as DL
import qualified Data.Map.Strict as DMS
import Data.Proxy
import Data.Text as T
import Data.Text.IO as T
import qualified Elminator.Elm19 as Elm19
import Elminator.Generics.Simple
import Elminator.Lib
import Language.Haskell.TH
import System.IO (FilePath)

-- | Include the elm source for the Haskell type specified by the proxy argument.
-- The second argument decides which components will be included and if the
-- generated type will be polymorphic.
include :: (ToHType a) => Proxy a -> GenOption -> Builder
include p dc = do
  let hType = SState.evalState (toHType p) (DMS.empty)
  mdata <-
    case hType of
      HUDef (UDefData m _ _ _) -> pure m
      HPrimitive _ -> error "Direct encoding of primitive type is not supported"
      HMaybe _ -> error "Direct encoding of maybe type is not supported"
      HList _ -> error "Direct encoding of list type is not supported"
      HTypeVar _ -> error "Unexpected meta data"
      HRecursive _ -> error "Unexpected meta data"
      HExternal _ _ -> error "Cannot generate code for external types"
  s <- get
  put $ DMS.insertWith (++) mdata [(dc, hType)] s

generateFor :: ElmVersion -> Options -> (Maybe FilePath) -> Builder -> Q Exp
generateFor ev opt mfp sc =
  let (_, gc) = runState sc DMS.empty
      r = do
        srcs <- mapM generateOne $ DMS.elems gc
        pure $ T.intercalate "" srcs
   in do (exprtxt, exinfo) <- runReaderT (runWriterT r) gc
         let fSrc = T.concat [Elm19.elmFront $ toImport exinfo, "\n\n", exprtxt]
         case mfp of
           Just fp -> runIO $ T.writeFile fp fSrc
           Nothing -> pure ()
         pure $ toExp fSrc
  where
    toImport :: [ExItem] -> Text
    toImport exs =
      let map_ =
            DL.foldr
              (\(ExItem m s) mp -> DMS.insertWith (++) m [s] mp)
              DMS.empty
              exs
       in T.intercalate "\n" $ DMS.foldrWithKey' foldFn [] map_
    foldFn :: Text -> [Text] -> [Text] -> [Text]
    foldFn mod_ smbs in_ =
      (T.concat ["import ", mod_, " exposing (", T.intercalate ", " smbs, ")"]) :
      in_
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
