{-# LANGUAGE OverloadedStrings #-}

module Elminator.Lib
  ( TypeDescriptor(..)
  , PolyConfig(..)
  , GenOption(..)
  , GenM
  , Decoder(..)
  , ConName
  , ConTag
  , ContentDecoder(..)
  , FieldName
  , FieldTag
  , ConstructorDescriptor(..)
  , Constructors
  , toTypeDescriptor
  , collectExtRefs
  , typeDescriptorToDecoder
  , renderTypeVar
  , Builder
  , ElmVersion(..)
  , renderTypeHead
  , renderType
  --, renderTHType
  , ReifyInfo(..)
  , nameToText
  , wrapInPara
  ) where

import Control.Monad.Reader as R
import Control.Monad.State.Lazy
import Control.Monad.Writer as W
import Data.Aeson
import qualified Data.List as DL
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.Map.Strict as DMS
import Data.Maybe
import Data.Text as T hiding (foldr)
import Elminator.Generics.Simple
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

data ContentDecoder
  = CDRecord [(FieldName, FieldTag, TypeDescriptor)]
  | CDRecordRaw (FieldName, FieldTag, TypeDescriptor)
  | CDList [TypeDescriptor]
  | CDRaw TypeDescriptor
  | CDEmpty
  deriving (Show)

type ConName = Text

type ConTag = Text

type FieldName = Text

type FieldTag = Text

-- Structure that we use to specify
-- both encoders and decoders.
data Decoder
  = DUnderConKey [(ConName, ConTag, ContentDecoder)]
  | DTagged Text Text [(ConName, ConTag, ContentDecoder)]
  | DTwoElement [(ConName, ConTag, ContentDecoder)]
  | DUntagged [(ConName, ContentDecoder)]

type GenM = WriterT [ExItem] (ReaderT (ElmVersion, GenConfig) Q)

-- | Decides wether the type definition will be polymorphic.
data PolyConfig
  = Mono
  | Poly
  deriving (Show)

-- | Decides which among type definiton, encoder and decoder
-- will be included for a type. The poly config value decides
-- wether the included type definition will be polymorphic.
data GenOption
  = Definiton PolyConfig
  | EncoderDecoder
  | Everything PolyConfig
  deriving (Show)

type GenConfig = DMS.Map MData ([GenOption], HType)

type Builder = State GenConfig ()

-- | Specify Elm version to generate code for
data ElmVersion
  = Elm0p18
  | Elm0p19

-- | Contains the type arguments of a type
-- | with info regarding if they are Phantom
-- | and the list of constructors from TH reifiy
data ReifyInfo =
  ReifyInfo [TypeVar] [Con]
  deriving (Show, Eq)

-- | Except for the reified info from TH, this type
-- holds more or less same info as HType
-- but it is arranged in a bit more accessable way for the
-- code that uses this information. 
data TypeDescriptor
  = TEmpty MData [TypeVar] [TypeDescriptor]
  | TOccupied MData ReifyInfo [TypeDescriptor] Constructors
  | TList TypeDescriptor
  | TMaybe TypeDescriptor
  | TTuple [TypeDescriptor]
  | TPrimitive MData
  | TRecusrive MData
  | TExternal (ExInfo TypeDescriptor)
  | TVar Name
  deriving (Show)

type Constructors = NE.NonEmpty ConstructorDescriptor

data ConstructorDescriptor
  = RecordConstructor Text (NE.NonEmpty (Text, TypeDescriptor))
  | SimpleConstructor Text (NE.NonEmpty TypeDescriptor)
  | NullaryConstructor Text
  deriving (Show)

getInfo :: Text -> GenM ([Name], [Con])
getInfo tnString =
  W.lift $
  R.lift $ do
    mName <- lookupTypeName $ unpack tnString
    case mName of
      Just tName -> do
        info <- reify tName
        pure (getTypeArgs info, getConstructors info)
      Nothing ->
        error $
        unpack $ T.concat ["Cannot find type with name ", tnString, " in scope"]

toTypeDescriptor :: HType -> GenM TypeDescriptor
toTypeDescriptor (HUDef udata) =
  case udata of
    UDefData mdata@(MData tnString _ _) targs hcons -> do
      tdArgs <- mapM toTypeDescriptor targs
      case isTuple tnString of
        Just _ -> pure $ TTuple tdArgs
        Nothing -> do
          (tVars, cnstrs) <- getInfo tnString
          case hcons of
            [] -> pure $ TEmpty mdata (Phantom <$> tVars) tdArgs
            (c:cs) -> do
              rawCons <-
                do h <- mkTdConstructor c
                   t <- mapM mkTdConstructor cs
                   pure $ h :| t
              let reifyInfo = ReifyInfo (mkTypeArg cnstrs <$> tVars) cnstrs
              pure $ TOccupied mdata reifyInfo tdArgs rawCons
toTypeDescriptor (HPrimitive md) = pure $ TPrimitive md
toTypeDescriptor (HList ht) = TList <$> toTypeDescriptor ht
toTypeDescriptor (HMaybe ht) = TMaybe <$> toTypeDescriptor ht
toTypeDescriptor (HRecursive m) = pure $ TRecusrive m
toTypeDescriptor (HExternal e) = do
  tds <- mapM toTypeDescriptor $ exTypeArgs e
  pure $ TExternal e {exTypeArgs = tds}

mkTdConstructor :: HConstructor -> GenM ConstructorDescriptor
mkTdConstructor hc =
  case hc of
    HConstructor (CName cname) fields ->
      case fields of
        [] -> pure $ NullaryConstructor cname
        hfields@(HField (Just _) _:_) ->
          let mapFn :: HField -> GenM (Text, TypeDescriptor)
              mapFn (HField Nothing _) = error "Unexpected unnamed field"
              mapFn (HField (Just n) x) = do
                td <- toTypeDescriptor x
                pure (n, td)
           in do a <- mapM mapFn hfields
                 pure $ RecordConstructor cname $ NE.fromList a
        hfields@(HField _ _:_) ->
          let mapFn :: HField -> GenM TypeDescriptor
              mapFn (HField _ td) = toTypeDescriptor td
           in do a <- mapM mapFn hfields
                 pure $ SimpleConstructor cname $ NE.fromList a

mkTypeArg :: [Con] -> Name -> TypeVar
mkTypeArg constrs name =
  if or $ searchCon name <$> constrs
    then Used name
    else Phantom name

searchCon :: Name -> Con -> Bool
searchCon name con = DL.or $ searchType name <$> getConstructorFields con
  where
    searchType :: Name -> Type -> Bool
    searchType name_ (VarT n) = name_ == n
    searchType name_ (AppT t1 t2) = searchType name_ t1 || searchType name_ t2
    searchType _ _ = False

getConstructorFields :: Con -> [Type]
getConstructorFields c =
  case c of
    (NormalC _ args) -> snd <$> args
    (RecC _ args) -> (\(_, _, x) -> x) <$> args
    _ -> error "Not implemented"

getConstructors :: Info -> [Con]
getConstructors info =
  case info of
    TyConI (DataD [] _ _ _ c _) -> c
    TyConI (NewtypeD _ _ _ _ c _) -> [c]
    x -> error $ "Unsupported type info" ++ show x

getTypeArgs :: Info -> [Name]
getTypeArgs i =
  case i of
    TyConI (DataD _ _ args _ _ _) -> mapFn <$> args
    TyConI (NewtypeD _ _ args _ _ _) -> mapFn <$> args
    _ -> error "Unimplemented"
  where
    mapFn :: TyVarBndr -> Name
    mapFn (PlainTV n) = n
    mapFn (KindedTV n _) = n

nameToText :: Name -> String
nameToText (Name (OccName a) _) = a

renderTypeHead :: TypeDescriptor -> Text
renderTypeHead td =
  case td of
    TEmpty md _ _ -> _mTypeName md
    TOccupied md _ _ _ -> _mTypeName md
    TRecusrive md -> _mTypeName md
    x -> error ("Unimplemented" ++ show x)

renderType :: TypeDescriptor -> Bool -> GenM Text
renderType td showPhantom = do
  hp <-
    case getMd td of
      Nothing -> pure True
      Just md -> hasPoly md
  if hp
    then case td of
           TEmpty md tvars targs -> do
             ta <- zipWithM renderFn targs tvars
             pure $ T.concat [_mTypeName md, " ", T.intercalate " " ta]
           TOccupied md (ReifyInfo tvars _) targs _ -> do
             ta <- zipWithM renderFn targs tvars
             pure $ T.concat [_mTypeName md, " ", T.intercalate " " ta]
           TList wtd -> do
             a <- renderType wtd showPhantom
             pure $ T.concat ["(List ", a, ")"]
           TMaybe wtd -> do
             a <- renderType wtd showPhantom
             pure $ T.concat ["(Maybe ", a, ")"]
           TTuple tds -> do
             ta <- mapM (flip renderType showPhantom) tds
             pure $ T.concat ["(", T.intercalate ", " ta, ")"]
           TPrimitive md -> pure $ _mTypeName md
           TRecusrive md -> pure $ _mTypeName md
           TExternal ei -> do
             ta <- mapM (flip renderType showPhantom) $ exTypeArgs ei
             pure $ T.concat [snd $ exType ei, " ", T.intercalate " " ta]
           TVar name -> pure $ pack $ nameToText name
    else pure $ renderTypeHead td
  where
    renderFn :: TypeDescriptor -> TypeVar -> GenM Text
    renderFn tdr (Phantom n) =
      if showPhantom
        then pure $ pack $ nameToText n
        else renderFn tdr (Used n)
    renderFn tdr (Used _) = renderType tdr showPhantom

wrapInPara :: Text -> Text
wrapInPara i = T.concat ["(", i, ")"]

--renderTHType :: Type -> GenM Text
--renderTHType (VarT n) = pure $ pack $ nameToText n
--renderTHType a@(AppT t1 t2) =
--  case findTuple a of
--    Just tx -> do
--      b <- mapM renderTHType tx
--      pure $ T.concat ["(", T.intercalate ", " b, ")"]
--    Nothing -> do
--      let rootType = getRootType a
--      hp <- hasPoly (MData rootType "" "")
--      if hp
--        then do
--          dt1 <- renderTHType t1
--          dt2 <- renderTHType t2
--          let dt2p =
--                case t2 of
--                  AppT _ _ -> T.concat ["(", dt2, ")"]
--                  _ -> dt2
--          pure $ T.concat [dt1, " ", dt2p]
--        else pure rootType
--renderTHType (ConT n) = pure $ pack $ nameToText n
--renderTHType _ = error "Not implemented"
--getRootType :: Type -> Text
--getRootType (ConT n) = pack $ nameToText n
--getRootType (VarT n) = pack $ nameToText n
--getRootType (AppT t1 _) = getRootType t1
--getRootType _ = error "Not implemented"
--findTuple :: Type -> Maybe [Type]
--findTuple (VarT _) = Nothing
--findTuple (ConT _) = Nothing
--findTuple (TupleT _) = Just []
--findTuple (AppT t1 t2) = do
--  xs <- findTuple t1
--  pure $ DL.reverse (t2 : xs)
--findTuple _ = error "Not implemented"
hasPoly :: MData -> GenM Bool
hasPoly tn = do
  (_, x) <- ask
  case DMS.lookup tn x of
    Just b -> pure $ hasPoly' b
    Nothing -> pure True
  where
    hasPoly' :: ([GenOption], HType) -> Bool
    hasPoly' (cl, _) = isJust $ DL.find fn cl
      where
        fn :: GenOption -> Bool
        fn (Definiton Poly) = True
        fn (Everything Poly) = True
        fn _ = False

renderTypeVar :: TypeVar -> Text
renderTypeVar (Used tv) = pack $ nameToText tv
renderTypeVar (Phantom tv) = pack $ nameToText tv

typeDescriptorToDecoder :: Options -> TypeDescriptor -> Decoder
typeDescriptorToDecoder opts td =
  case td of
    TEmpty {} -> error "Cannot make decoder for Empty type"
    TOccupied _ _ _ cnstrs -> gdConstructor cnstrs opts
    _ -> error "Cannot only make decoders for user defined types"

gdConstructor :: Constructors -> Options -> Decoder
gdConstructor (cd :| []) opts =
  if tagSingleConstructors opts
    then gdTaggedWithConstructor [cd] opts
    else DUntagged [(getCName cd, mkContentDecoder cd opts)]
gdConstructor cds opts = gdTaggedWithConstructor (NE.toList cds) opts

gdTaggedWithConstructor :: [ConstructorDescriptor] -> Options -> Decoder
gdTaggedWithConstructor cds opts =
  case sumEncoding opts of
    TaggedObject tfn cfn -> DTagged (pack tfn) (pack cfn) cdPair
    ObjectWithSingleField -> DUnderConKey cdPair
    TwoElemArray -> DTwoElement cdPair
    UntaggedValue ->
      DUntagged $ (\cd -> (getCName cd, mkContentDecoder cd opts)) <$> cds
  where
    cdPair :: [(ConName, ConTag, ContentDecoder)]
    cdPair =
      (\cd ->
         ( getCName cd
         , pack $ constructorTagModifier opts $ unpack $ getCName cd
         , mkContentDecoder cd opts)) <$>
      cds

mkContentDecoder :: ConstructorDescriptor -> Options -> ContentDecoder
mkContentDecoder cd opts =
  case cd of
    RecordConstructor _cname (nf :| []) ->
      if unwrapUnaryRecords opts
        then case sumEncoding opts of
               ObjectWithSingleField -> CDRecordRaw $ modifyFieldLabel nf
               TwoElemArray -> CDRecordRaw $ modifyFieldLabel nf
               UntaggedValue -> CDRecordRaw $ modifyFieldLabel nf
               TaggedObject _ _ -> CDRecord [modifyFieldLabel nf]
        else CDRecord [modifyFieldLabel nf]
    RecordConstructor _cname nf ->
      CDRecord $ NE.toList $ NE.map modifyFieldLabel nf
    SimpleConstructor _cname (f :| []) -> CDRaw f
    SimpleConstructor _cname f -> CDList $ NE.toList f
    NullaryConstructor _ -> CDEmpty
  where
    modifyFieldLabel ::
         (Text, TypeDescriptor) -> (FieldName, FieldTag, TypeDescriptor)
    modifyFieldLabel (a, b) = (a, pack $ fieldLabelModifier opts $ unpack a, b)

getCName :: ConstructorDescriptor -> Text
getCName (RecordConstructor x _) = x
getCName (SimpleConstructor x _) = x
getCName (NullaryConstructor x) = x

collectExtRefs :: TypeDescriptor -> GenM ()
collectExtRefs (TExternal (ExInfo ei (Just en) (Just de) _)) = tell [ei, en, de]
collectExtRefs (TExternal (ExInfo ei _ _ _)) = tell [ei]
collectExtRefs (TEmpty _ _ targs) = mapM_ collectExtRefs targs
collectExtRefs (TOccupied _ _ _ cons_) =
  mapM_ collectExtRefs $ getConstructorsFields cons_
collectExtRefs (TList td) = collectExtRefs td
collectExtRefs (TMaybe td) = collectExtRefs td
collectExtRefs (TPrimitive _) = pure ()
collectExtRefs (TRecusrive _) = pure ()
collectExtRefs _ = pure ()

getConstructorsFields :: Constructors -> [TypeDescriptor]
getConstructorsFields nec =
  DL.concat $ NE.toList $ NE.map getConstructorFields_ nec

getConstructorFields_ :: ConstructorDescriptor -> [TypeDescriptor]
getConstructorFields_ (RecordConstructor _ nef) = snd <$> NE.toList nef
getConstructorFields_ (SimpleConstructor _ f) = NE.toList f
getConstructorFields_ (NullaryConstructor _) = []

getMd :: TypeDescriptor -> Maybe MData
getMd td =
  case td of
    TEmpty md _ _ -> Just md
    TOccupied md _ _ _ -> Just md
    TPrimitive md -> Just md
    TRecusrive md -> Just md
    _ -> Nothing
