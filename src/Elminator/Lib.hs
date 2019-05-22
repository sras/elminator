{-# LANGUAGE OverloadedStrings #-}

module Elminator.Lib where

import Control.Monad.Reader as R
import Control.Monad.State.Lazy
import Control.Monad.Writer as W
import Data.Aeson
import qualified Data.List as DL
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.List.NonEmpty as NE
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

type LibM = WriterT [ExItem] (ReaderT GenConfig Q)

-- | Decides wether the type definition will be polymorphic.
data PolyConfig
  = Mono
  | Poly
  deriving (Show)

-- | Decides which among type definiton, encoder and decoder
-- will be included for a type. The poly config value decides
-- wether the included type definition will be poly morphic.
data GenOption
  = Definiton PolyConfig
  | EncoderDecoder
  | Everything PolyConfig
  deriving (Show)

type GenConfig = DMS.Map MData [(GenOption, HType)]

type Builder = State GenConfig ()

-- | Specify Elm version to generate code for
data ElmVersion =
  Elm19

data TypeDescriptor
  = SimpleType CTData
  | Polymorphic [TypeVar] CTData
  | List TypeDescriptor
  | TDMaybe TypeDescriptor
  | Primitive Text Text
  | TRecusrive MData
  | TExternal ExInfo TypeName
  | TTypeVar Name
  deriving (Show, Eq)

data TypeName =
  TypeName
    { tnHead :: Text -- Just the type name without type parameters
    , tnFull :: Text -- Full concrete type with concrete type parameters
    , tnPhantom :: Text -- Same as above but with type variables where type variable is phantom
    , tnMData :: MData
    }
  deriving (Show, Eq)

data CTData
  = CTData TypeName Constructors
  | CTEmpty TypeName
  deriving (Show, Eq)

type Constructors = (NE.NonEmpty ConstructorDescriptor)

data ConstructorDescriptor
  = RecordConstructor Text (Fields NamedField)
  | SimpleConstructor Text (Fields TypeDescriptor)
  | NullaryConstructor Text
  deriving (Show, Eq)

type Fields a = NE.NonEmpty a

data NamedField =
  NamedField Text TypeDescriptor
  deriving (Show, Eq)

getCTDName :: CTData -> Text
getCTDName (CTData a _) = tnHead a
getCTDName _ = error "Unimpl"

-- Takes an HType, refies the corresponding
-- type using template haskell, and inserts type arguments
-- from the original type into the corresponding types in the
-- constructor fields, replacing the concrete types there.
-- Imagine we have type, defined as follows;
-- 
-- data MyWeirdType a b c = C1 (Maybe (Either a Int)) | C2 (Either a b)
-- 
-- When a value of this type appear in a field in another type, say
--
-- data MyWeirdType2 a = D1 (Maybe a)
-- 
-- and consider that we have a value of type, MyWeirdType2 (MyWeirdType2 Int String Float)
-- The HType of this type will be something like
--
-- HUDef (UDefData (MData MyWeirdType2..) [
--     HUDef (UDefData (MData MyWeirdType ..) [HType Int, HType String, HType Float] Nothing
--       [HConstructor C1 [HField Nothing (HType of (Maybe (Either Int Int)))], HConstructor C2 [..]])])
--
--This function walks this tree of HTypes and overwrites the HTypes that comes at a type variable location
--with a HTypeVar value. So the Htype returned would be something like
--
-- HUDef (UDefData (MData MyWeirdType2..) [
--     HUDef (UDefData (MData MyWeirdType ..) [HType Int, HType String, HType Float] Nothing
--       [HConstructor C1 [HField Nothing (HType of (Maybe (Either (HTypeVar a) Int)))], HConstructor C2 [..]])])
--Thus leaving the rest of the information in the HType value (including the concrete types this type was initialized with) alone.
mkPolyMorphic :: HType -> LibM HType
mkPolyMorphic _htype@(HUDef (UDefData (MData tnString a b) targs _ hcons)) = do
  mtName <- W.lift $ R.lift $ lookupTypeName $ unpack tnString
  case mtName of
    Just tName -> do
      info <- W.lift $ R.lift $ reify tName
      let tVars = getTypeArgs info
        -- take each type variable 
        -- and walk through all constructors 
        -- replacing HType's in fields with an
        -- HTypeVar value where it matches.
          constrs = (getConstructors info)
          polyCons = foldr (mkPolyMorphicConstructor constrs) hcons tVars
      pure $
        HUDef $
        UDefData
          (MData tnString a b)
          targs
          (Just $ mkTypeArg constrs <$> tVars)
          polyCons
    Nothing ->
      error $
      unpack $ T.concat ["Cannot find type with name ", tnString, " in scope"]
  where
    mkTypeArg :: [Con] -> Name -> TypeVar
    mkTypeArg constrs name =
      if DL.any id $ searchCon name <$> constrs
        then Used name
        else Phantom name
    searchCon :: Name -> Con -> Bool
    searchCon name con =
      DL.any id $ searchType name <$> (getConstructorFields con)
      where
        searchType :: Name -> Type -> Bool
        searchType name_ (VarT n) = name_ == n
        searchType name_ (AppT t1 t2) =
          (searchType name_ t1) || (searchType name_ t2)
        searchType _ _ = False
    mkPolyMorphicConstructor ::
         [Con] -> Name -> [HConstructor] -> [HConstructor]
    mkPolyMorphicConstructor cons_ tvName hcons_ =
      DL.zipWith (mkPolyMorphicConstructor_ tvName) hcons_ cons_
      where
        mkPolyMorphicConstructor_ :: Name -> HConstructor -> Con -> HConstructor
        mkPolyMorphicConstructor_ tvName_ (HConstructor cn fields) con =
          HConstructor cn $
          DL.zipWith
            (mkPolyMorphicField tvName_)
            fields
            (getConstructorFields con)
        mkPolyMorphicField :: Name -> HField -> Type -> HField
        mkPolyMorphicField _tvName (HField fn ht) t =
          HField fn (insertTVar tvName ht t)
        insertTVar :: Name -> HType -> Type -> HType
        insertTVar tvname h (VarT n) =
          if n == tvname
            then (HTypeVar n)
            else h
        insertTVar tvname (HUDef udefd) typ =
          let taList = DL.reverse $ udefdTypeArgs udefd
           in HUDef $
              udefd {udefdTypeArgs = DL.reverse $ insertInHL tvname taList typ}
        insertTVar tvname (HExternal ei targs_) typ =
          let taList = DL.reverse targs_
           in HExternal ei $ DL.reverse $ insertInHL tvname taList typ
        insertTVar tvname (HList ht) (AppT ListT t) =
          HList (insertTVar tvname ht t)
        insertTVar tvname (HMaybe ht) (AppT _ t) =
          HMaybe (insertTVar tvname ht t)
        insertTVar _ x _ = x
        insertInHL :: Name -> [HType] -> Type -> [HType]
        insertInHL tvname (h:hs) (AppT t1 t2) =
          (insertTVar tvname h t2) : (insertInHL tvname hs t1)
        insertInHL _ hs _ = hs
    getConstructorFields :: Con -> [Type]
    getConstructorFields c =
      case c of
        (NormalC _ args) -> snd <$> args
        (RecC _ args) -> (\(_, _, x) -> x) <$> args
        _ -> error "Not implemented"
mkPolyMorphic _ = error "Not implemented"

dropPackagePrefix :: String -> String
dropPackagePrefix x = DL.reverse $ DL.takeWhile (/= '.') $ DL.reverse x

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

renderHType :: HType -> Text
renderHType htype = renderHType_ htype True

renderHType_ :: HType -> Bool -> Text
renderHType_ h@(HUDef u) incParen =
  if incParen
    then if DL.length (udefdTypeArgs u) > 0
           then T.concat ["(", renderHType_ h False, ")"]
           else renderHType_ h False
    else case (udefdTypeVars u) of
           Just tvars ->
             let typeName = _mTypeName $ udefdMdata u
              in if isJust $ isTuple typeName
                   then renderTuple $ (udefdTypeArgs u)
                   else T.intercalate " " $
                        typeName :
                        (DL.zipWith renderTypeParam (udefdTypeArgs u) tvars)
           Nothing ->
             let typeName = _mTypeName $ udefdMdata u
              in if isJust $ isTuple typeName
                   then renderTuple $ (udefdTypeArgs u)
                   else T.intercalate " " $
                        (_mTypeName $ udefdMdata u) :
                        (renderHType <$> (udefdTypeArgs u))
  where
    renderTuple :: [HType] -> Text
    renderTuple [] = "()"
    renderTuple args = T.concat [T.intercalate ", " (renderHType <$> args)]
    renderTypeParam :: HType -> TypeVar -> Text
    renderTypeParam ht tv =
      case tv of
        Phantom n -> pack $ nameToText n
        Used _ -> (renderHType ht)
renderHType_ (HPrimitive md) _ = _mTypeName md
renderHType_ (HList t) _ = T.concat ["(List ", renderHType_ t True, ")"]
renderHType_ (HTypeVar t) _ = pack $ nameToText t
renderHType_ (HMaybe ht) _ = T.concat ["(Maybe ", renderHType_ ht True, ")"]
renderHType_ (HRecursive md) _ = _mTypeName md
renderHType_ (HExternal ei ta) _ =
  T.concat [extSymbol $ exType ei, " ", T.intercalate " " (renderHType <$> ta)]

toTypeDescriptor :: HType -> TypeDescriptor
toTypeDescriptor ht@(HUDef (udef@(UDefData mdata@(MData tnString _ _) (_:_) (Just tv) x))) =
  Polymorphic tv $
  let rendered = (renderHType $ HUDef $ udef {udefdTypeVars = Nothing})
      renderedPhantom = renderHType ht
   in case x of
        [] -> CTEmpty (TypeName tnString rendered renderedPhantom mdata)
        (a:as) ->
          CTData (TypeName tnString rendered renderedPhantom mdata) $
          toConstructors (a :| as)
toTypeDescriptor ht@(HUDef (UDefData mdata@(MData tnString _ _) _ _ x)) =
  SimpleType $
  let rendered = (renderHType ht)
   in case x of
        [] -> CTEmpty (TypeName tnString rendered rendered mdata)
        (a:as) ->
          CTData (TypeName tnString rendered rendered mdata) $
          toConstructors (a :| as)
toTypeDescriptor ht@(HPrimitive (MData tnString _ _)) =
  Primitive tnString (renderHType ht)
toTypeDescriptor (HList t) = List (toTypeDescriptor t)
toTypeDescriptor (HMaybe t) = TDMaybe (toTypeDescriptor t)
toTypeDescriptor (HRecursive md) = TRecusrive $ md
toTypeDescriptor ht@(HExternal ei _) =
  let rendered = (renderHType $ HExternal ei [])
      renderedPhantom = (renderHType ht)
   in TExternal ei $
      (TypeName (extSymbol $ exType $ ei) rendered renderedPhantom $
       MData "" "" "")
toTypeDescriptor (HTypeVar n) = TTypeVar n

toConstructors :: NE.NonEmpty HConstructor -> Constructors
toConstructors x = NE.map mkConstructorDesc x

mkConstructorDesc :: HConstructor -> ConstructorDescriptor
mkConstructorDesc (HConstructor (CName cname) fs) =
  case fs of
    [] -> NullaryConstructor cname
    (hf@(HField (Just _) _):hfs) ->
      RecordConstructor cname $ mkRecordFields (hf NE.:| hfs)
    (hf@(HField Nothing _):hfs) ->
      SimpleConstructor cname $ mkUnNamedFields (hf NE.:| hfs)

mkRecordFields :: NE.NonEmpty HField -> Fields NamedField
mkRecordFields x = NE.map mkRecordField x

mkRecordField :: HField -> NamedField
mkRecordField (HField (Just x) htype) = NamedField x (toTypeDescriptor htype)
mkRecordField _ = error "Incompatible field to make a named field"

mkUnNamedFields :: NE.NonEmpty HField -> Fields TypeDescriptor
mkUnNamedFields x = NE.map mkUnNamedField x

mkUnNamedField :: HField -> TypeDescriptor
mkUnNamedField (HField _ htype) = toTypeDescriptor htype

getRenderedName :: TypeDescriptor -> Text
getRenderedName (SimpleType c) = getRenderedNameFromCTdata c
getRenderedName (Polymorphic _ c) = getRenderedNameFromCTdata c
getRenderedName (List h) = T.concat ["(List ", getRenderedName h, ")"]
getRenderedName (TDMaybe h) = T.concat ["(Maybe ", getRenderedName h, ")"]
getRenderedName (Primitive _ c) = c
getRenderedName (TRecusrive md) = _mTypeName md
getRenderedName (TExternal _ x) = tnPhantom x
getRenderedName (TTypeVar x) = pack $ nameToText x

getRenderedNameFromCTdata :: CTData -> Text
getRenderedNameFromCTdata (CTData x _) = tnPhantom x
getRenderedNameFromCTdata (CTEmpty x) = tnFull x

renderTypeVar :: TypeVar -> Text
renderTypeVar (Used tv) = pack $ nameToText tv
renderTypeVar (Phantom tv) = pack $ nameToText tv

typeDescriptorToDecoder :: Options -> TypeDescriptor -> Decoder
typeDescriptorToDecoder opts td =
  case td of
    SimpleType ctdata -> ctdataToDecoder ctdata
    Polymorphic _ ctdata -> ctdataToDecoder ctdata
    _ -> error "Cannot only make decoders for user defined types"
  where
    ctdataToDecoder :: CTData -> Decoder
    ctdataToDecoder (CTData _ crs) = gdConstructor crs opts
    ctdataToDecoder (CTEmpty _) = error "Cannot make decoder for Empty type"

gdConstructor :: Constructors -> Options -> Decoder
gdConstructor (cd :| []) opts =
  if tagSingleConstructors opts
    then gdTaggedWithConstructor [cd] opts
    else DUntagged $ [(getCName cd, mkContentDecoder cd opts)]
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
    SimpleConstructor _cname f -> CDList $ NE.toList $ f
    NullaryConstructor _ -> CDEmpty
  where
    modifyFieldLabel :: NamedField -> (FieldName, FieldTag, TypeDescriptor)
    modifyFieldLabel (NamedField a b) =
      (a, pack $ fieldLabelModifier opts $ unpack $ a, b)

getCName :: ConstructorDescriptor -> Text
getCName (RecordConstructor x _) = x
getCName (SimpleConstructor x _) = x
getCName (NullaryConstructor x) = x

collectExtRefs :: TypeDescriptor -> LibM ()
collectExtRefs (TExternal (ExInfo ei (Just en) (Just de)) _) = tell [ei, en, de]
collectExtRefs (TExternal (ExInfo ei _ _) _) = tell [ei]
collectExtRefs (SimpleType (CTData _ cons_)) =
  mapM_ collectExtRefs $ getConstructorsFields cons_
collectExtRefs (Polymorphic _ (CTData _ cons_)) =
  mapM_ collectExtRefs $ getConstructorsFields cons_
collectExtRefs (List td) = collectExtRefs td
collectExtRefs (TDMaybe td) = collectExtRefs td
collectExtRefs (Primitive _ _) = pure ()
collectExtRefs (TRecusrive _) = pure ()
collectExtRefs _ = pure ()

getConstructorsFields :: Constructors -> [TypeDescriptor]
getConstructorsFields nec =
  DL.concat $ NE.toList $ NE.map getConstructorFields_ nec

getConstructorFields_ :: ConstructorDescriptor -> [TypeDescriptor]
getConstructorFields_ (RecordConstructor _ nef) =
  (\(NamedField _ td) -> td) <$> NE.toList nef
getConstructorFields_ (SimpleConstructor _ f) = NE.toList f
getConstructorFields_ (NullaryConstructor _) = []
