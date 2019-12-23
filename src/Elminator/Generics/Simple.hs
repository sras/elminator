{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}

module Elminator.Generics.Simple where

import Control.Monad.State.Strict
import qualified Data.List as DL
import qualified Data.Map.Strict as DMS
import Data.Proxy
import Data.String
import Data.Kind
import Data.Text (Text, pack)
import qualified Data.Text as T
import Data.Typeable
import GHC.Generics
import GHC.TypeLits
import Language.Haskell.TH hiding (Type)

newtype CName =
  CName Text
  deriving (Show)

data HField =
  HField (Maybe Text) HType
  deriving (Show)

type HState = State (DMS.Map MData ())

type ExTypeName = Text

type ExEncoderName = Text

type ExDecoderName = Text

type ModuleName = Text

type SymbolName = Text

type ExItem = (ModuleName, SymbolName)

data ExInfo a =
  ExInfo
    { exType :: ExItem
    , exEncoder :: Maybe ExItem
    , exDecoder :: Maybe ExItem
    , exTypeArgs :: [a]
    }
  deriving (Show)

data MData =
  MData
    { _mTypeName :: Text
    , _mModuleName :: Text
    , _mPackageName :: Text
    }
  deriving (Show, Ord, Eq)

instance IsString MData where
  fromString x = MData (pack x) "" ""

data HConstructor =
  HConstructor CName [HField]
  deriving (Show)

data TypeVar
  = Used Name
  | Phantom Name
  deriving (Eq, Show)

data UDefData =
  UDefData
    { udefdMdata :: MData
    , udefdTypeArgs :: [HType]
    , udefDConstructors :: [HConstructor]
    }
  deriving (Show)

-- | This type holds the type information we get from generics.
-- Only the `HExternal` constructor is supposed to be used by the programmer
-- to implement `ToHType` instances for entites that are predefined in Elm. A sample can be seen below.
--
-- Here, let `MyExtType a b` be a type which has the corresponding type, encoders and decoders predefined in Elm
-- in a module named "Lib". Here is how you can implement a ToHType instance for this type so that your other
-- autogenerated types can have fields of type `MyExtType a b`.
--
-- @
--
-- instance (ToHType a, ToHType b) => ToHType (MyExtType a b) where
--   toHType _ = do
--     ha <- toHType (Proxy :: Proxy a)
--     hb <- toHType (Proxy :: Proxy b)
--     pure $
--       HExternal
--         (ExInfo
--            ("External", "MyExtType")
--            (Just ("External", "encodeMyExtType"))
--            (Just ("External", "decodeMyExtType"))
--            [ha, hb])
--
-- @
--
data HType
  = HUDef UDefData
  | HMaybe HType
  | HList HType
  | HPrimitive MData
  | HRecursive MData
  | HExternal (ExInfo HType)
  deriving (Show)

class ToHType_ (f :: Type -> Type) where
  toHType_ :: Proxy f -> HState HType

class ToHField_ (f :: Type -> Type) where
  toHField_ :: Proxy f -> HState [HField]

class ToHConstructor_ (f :: Type -> Type) where
  toHConstructor_ :: Proxy f -> HState [HConstructor]

type family ExtractTArgs (f :: k) :: [Type] where
  ExtractTArgs ((b :: Type -> k) a) = a : ExtractTArgs b
  ExtractTArgs f = '[]

class ToHTArgs f where
  toHTArgs :: Proxy f -> [HState HType]

instance ToHTArgs '[] where
  toHTArgs _ = []

instance (ToHType a, ToHTArgs x) => ToHTArgs (a : x) where
  toHTArgs _ = toHType (Proxy :: Proxy a) : toHTArgs (Proxy :: Proxy x)

class ToHType f where
  toHType :: Proxy f -> HState HType
  default toHType :: (ToHTArgs (ExtractTArgs f), Generic f, ToHType_ (Rep f)) =>
    Proxy f -> HState HType
  toHType _ = do
    targs <- sequence (toHTArgs (Proxy :: Proxy (ExtractTArgs f)))
    htype <- toHType_ (Proxy :: (Proxy (Rep f)))
    pure $
      case htype of
        HUDef ud -> HUDef $ ud {udefdTypeArgs = DL.reverse targs}
        a -> a

instance (ToHConstructor_ b, KnownSymbol a1, KnownSymbol a2, KnownSymbol a3) =>
         ToHType_ (D1 ('MetaData a1 a2 a3 a4) b) where
  toHType_ _ =
    let mdata =
          MData
            (pack $ symbolVal (Proxy :: Proxy a1))
            (pack $ symbolVal (Proxy :: Proxy a2))
            (pack $ symbolVal (Proxy :: Proxy a3))
     in do seen <- get
           case DMS.lookup mdata seen of
             Just _ -> pure $ HRecursive mdata
             Nothing -> do
               case isTuple $ _mTypeName mdata of
                 Just _ -> pure ()
                 Nothing -> put $ DMS.insert mdata () seen
               cons_ <- toHConstructor_ (Proxy :: Proxy b)
               pure $ HUDef $ UDefData mdata [] cons_

isTuple :: Text -> Maybe Int
isTuple t =
  case T.uncons t of
    Just (c, _) ->
      if c == '('
        then Just $ DL.length $ T.split (== ',') t
        else Nothing
    _ -> Nothing

instance ToHConstructor_ V1 where
  toHConstructor_ _ = pure []

instance (KnownSymbol cname, ToHField_ s) =>
         ToHConstructor_ (C1 ('MetaCons cname a b) s) where
  toHConstructor_ _ = do
    hfield <- toHField_ (Proxy :: Proxy s)
    pure [HConstructor (CName $ pack $ symbolVal (Proxy :: Proxy cname)) hfield]

instance ToHField_ U1 where
  toHField_ _ = pure []

instance (KnownSymbol cname, ToHType_ w) =>
         ToHField_ (S1 ('MetaSel ('Just cname) a b c) w) where
  toHField_ _ = do
    htype <- toHType_ (Proxy :: Proxy w)
    pure [HField (Just $ pack $ symbolVal (Proxy :: Proxy cname)) htype]

instance (ToHType_ w) => ToHField_ (S1 ('MetaSel 'Nothing a b c) w) where
  toHField_ _ = do
    htype <- toHType_ (Proxy :: Proxy w)
    pure [HField Nothing htype]

instance (ToHField_ a, ToHField_ b) => ToHField_ (a :*: b) where
  toHField_ _ = do
    hfield1 <- toHField_ (Proxy :: Proxy a)
    hfield2 <- toHField_ (Proxy :: Proxy b)
    pure $ hfield1 ++ hfield2

instance (ToHConstructor_ a, ToHConstructor_ b) =>
         ToHConstructor_ (a :+: b) where
  toHConstructor_ _ = do
    lhs <- toHConstructor_ (Proxy :: Proxy a)
    rhs <- toHConstructor_ (Proxy :: Proxy b)
    pure $ lhs ++ rhs

instance (ToHType a) => ToHType_ (K1 R a) where
  toHType_ _ = toHType (Proxy :: Proxy a)

instance {-# OVERLAPPABLE #-} (Typeable a) => ToHType a where
  toHType p = pure $ mkHType p

-- Common types
instance (ToHType a, ToHType b) => ToHType (Either a b)

instance (ToHType a) => ToHType (Maybe a) where
  toHType _ = do
    htype <- toHType (Proxy :: Proxy a)
    pure $ HMaybe htype

-- We need these tuple instances despite of the general ToHType instance
-- because we need to special case tupless to exclude them from recursion
-- tracking, which is included in the default implementation if ToHType class
instance ToHType ()

instance (ToHType a1, ToHType a2) => ToHType (a1, a2)

instance (ToHType a1, ToHType a2, ToHType a3) => ToHType (a1, a2, a3)

instance (ToHType a1, ToHType a2, ToHType a3, ToHType a4) =>
         ToHType (a1, a2, a3, a4)

instance (ToHType a1, ToHType a2, ToHType a3, ToHType a4, ToHType a5) =>
         ToHType (a1, a2, a3, a4, a5)

instance ( ToHType a1
         , ToHType a2
         , ToHType a3
         , ToHType a4
         , ToHType a5
         , ToHType a6
         ) =>
         ToHType (a1, a2, a3, a4, a5, a6)

instance ( ToHType a1
         , ToHType a2
         , ToHType a3
         , ToHType a4
         , ToHType a5
         , ToHType a6
         , ToHType a7
         ) =>
         ToHType (a1, a2, a3, a4, a5, a6, a7)

instance (ToHType a) => ToHType [a] where
  toHType _ = do
    htype <- toHType (Proxy :: Proxy a)
    pure $
      case htype of
        HPrimitive md@(MData "Char" _ _) ->
          HPrimitive $ md {_mTypeName = "String"}
        hta -> HList hta

instance ToHType Text where
  toHType _ = toHType (Proxy :: Proxy String)

mkHType :: (Typeable a) => Proxy a -> HType
mkHType p =
  let tname = typeRepTyCon $ typeRep p
   in HPrimitive
        (MData
           (pack $ tyConName tname)
           (pack $ tyConModule tname)
           (pack $ tyConPackage tname))
