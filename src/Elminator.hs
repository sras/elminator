{-# LANGUAGE OverloadedStrings #-}

{-|

Generate Elm type definitions, encoders and decoders from Haskell data types.

@
  \{\-\#Language ScopedTypeVariables\#-\}
  \{\-\#Language FlexibleInstances\#-\}
  \{\-\#Language DeriveAnyClass\#-\}
  \{\-\#Language OverloadedStrings\#-\}

  module Lib  where

  import Elminator
  import GHC.Generics

  data SingleCon = SingleCon (Maybe Int) String deriving (Generic, ToHType)
  data WithMaybesPoly a b =
    WithMaybesPoly
      { mbpF1 :: Maybe a
      , mbpF2 :: Maybe b
      }
    deriving (Generic, ToHType)

@

Here is how we generate Elm source for the above defined types.

@
\{\-\#Language OverloadedStrings\#-\}
\{\-\#Language TemplateHaskell\#-\}

module CodeGen where

import Data.Proxy
import Elminator
import Data.Text

import Lib

elmSource :: Text
elmSource = $(generateFor Elm19 myDefaultOptions (Just ".\/elm-app\/src\/Autogen.elm") $ do
  include (Proxy :: Proxy SingleCon) $ Everything Mono
  include (Proxy :: Proxy (WithMaybesPoly (Maybe String) Float)) $ Definiton Poly

@
-}
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
  let hType = SState.evalState (toHType p) DMS.empty
  mdata <-
    case hType of
      HUDef (UDefData m _ _) -> pure m
      HPrimitive _ -> error "Direct encoding of primitive type is not supported"
      HMaybe _ -> error "Direct encoding of maybe type is not supported"
      HList _ -> error "Direct encoding of list type is not supported"
      HRecursive _ -> error "Unexpected meta data"
      HExternal _ _ -> error "Cannot generate code for external types"
  s <- get
  put $ DMS.insertWith (\(a, b) (ea, _) -> (ea ++ a, b)) mdata ([dc], hType) s

-- | Return the generated Elm code in a template haskell splice and optionally
-- write to a Elm source file at the same time. The second argument is the Options type
-- from Aeson library. Use `include` calls to build the `Builder` value.
generateFor :: ElmVersion -> Options -> Maybe FilePath -> Builder -> Q Exp
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
      T.concat ["import ", mod_, " exposing (", T.intercalate ", " smbs, ")"] :
      in_
    toExp :: Text -> Exp
    toExp t = LitE $ StringL $ unpack t
    generateOne :: ([GenOption], HType) -> LibM Text
    generateOne (gs, ht) = do
      srcs <- mapM (generateOne_ ht) gs
      pure $ T.intercalate "" srcs
      where
        generateOne_ :: HType -> GenOption -> LibM Text
        generateOne_ h d =
          case ev of
            Elm19 -> Elm19.generateElm d h opt
