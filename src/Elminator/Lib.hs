{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module Elminator.Lib where

import Generics.Simple
import Data.Text as T
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import qualified Data.List as DL
import qualified Data.Map.Strict as DMS
import Data.Maybe
import Control.Monad.Reader as R
import Control.Monad.State.Lazy
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.List.NonEmpty as NE
import Data.String

data ContentDecoder
  = CDRecord [(FieldName, FieldTag, TypeDescriptor)]
  | CDRecordRaw (FieldName, FieldTag, TypeDescriptor)
  | CDList [TypeDescriptor]
  | CDRaw TypeDescriptor
  | CDEmpty

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

type LibM = ReaderT GenConfig Q

type CurrentPos = Int
type CurrentIndent = Int

type RenderM = State (CurrentIndent, CurrentPos, Text)

renderElm :: ElmSrc -> Text
renderElm (ElmSrc decs) = let
  (_, _, srcs) = execState (mapM_ (\x -> do renderElmDec x; renderNL; renderNL;resetIndent) decs) (0, 0, "")
  in srcs

renderText :: Text -> RenderM ()
renderText t = do
  (ci, cp, ct) <- get
  put (ci, cp + T.length t, T.concat [ct, t])

renderIC :: RenderM () -> [a] -> (a -> RenderM ()) -> RenderM ()
renderIC _ [] _ = pure ()
renderIC _ [t] fn = fn t
renderIC s (t:tx) fn = do
  fn t
  sequence_ $ (\x -> do; s; fn x;) <$> tx

renderNL :: RenderM ()
renderNL = do
  renderText "\n"
  modify (\(i, _, t) -> (i, 0, t))

getCI :: RenderM Int
getCI = do
  (i, _, _) <- get
  pure i

getCP :: RenderM Int
getCP = do
  (_, p, _) <- get
  pure p

setCI :: Int -> RenderM ()
setCI i =
  modify (\(_, p, t) -> (i, p, t))

resetIndent :: RenderM ()
resetIndent = setCI 0

incIndent :: RenderM ()
incIndent = do
  modify (\(i, p, t) -> (i+1, p, t))

renderCI :: RenderM ()
renderCI = do
  i <- getCI
  renderText $ getIntend i

renderSpace :: RenderM ()
renderSpace = renderText " "

renderElmDec :: EDec -> RenderM ()
renderElmDec (EType name targs cons_) = do
  renderCI
  renderText "type "
  renderSpace
  renderText name 
  renderSpace 
  renderIC (renderSpace) targs renderText
  renderSpace 
  renderText "=" 
  renderSpace 
  renderCon cons_
  resetIndent
renderElmDec (EFunc name sig fargs expr) = do
  case sig of
    Just s -> renderText $ T.concat [name , " : ", s]
    Nothing -> pure ()
  renderNL
  renderCI
  renderText name
  renderSpace
  renderIC (renderSpace) fargs renderText
  renderText " = "
  renderNL
  incIndent
  renderCI
  renderExp expr

renderExp :: EExpr -> RenderM () 
renderExp (ERec fields) = do
  renderText "{"
  renderIC (renderText ", ") fields renderField
  renderText "}"
  where
    renderField (fname, exp_) = do
      renderText fname
      renderText " = "
      renderExp exp_
renderExp (ELet decs exp_) = do
  i0 <- getCI
  p <- getCP
  renderText $ "let"
  setCI $ p + 1
  i <- getCI
  renderIC (do;renderNL;renderCI) decs renderElmDec
  renderNL
  setCI (i - 1)
  renderCI
  renderText "in"
  renderSpace
  renderExp exp_
  setCI i0
renderExp (ECase expr branches) = do
  si <- getCI
  renderText "case"
  renderSpace
  renderExp expr
  renderSpace
  renderText "of"
  renderNL
  setCI (si + 1)
  renderCI
  renderIC (do;renderNL;renderCI) branches renderCaseBranch
renderExp (EFuncApp expr1 expr2) = do
  renderExp expr1
  renderSpace
  renderText "("
  renderExp expr2
  renderText ")"
renderExp (EInlineApp op expr1 expr2) = do
  renderText "("
  renderExp expr1
  renderText ")"
  renderSpace
  renderExp op
  renderText "("
  renderExp expr2
  renderText ")"
renderExp (EName n) = renderText n
renderExp (EList l) = do
  i <- getCI
  p <- getCP
  renderText "[ "
  renderIC (do;renderNL; setCI p; renderCI; renderText ", ") l renderExp
  renderText "]"
  setCI i
renderExp (ELiteral l) = renderLiteral l
renderExp (ETuple l) = do
  renderText "("
  renderIC (renderText ", ") l renderExp
  renderText ")"

renderLiteral :: ELit -> RenderM ()
renderLiteral (EStringL s) = renderText $ pack $ show s
renderLiteral (EIntL x) = renderText $ pack $ show x

renderCaseBranch :: ECaseBranch -> RenderM ()
renderCaseBranch (pattern, expr) = do
  renderPattern pattern
  renderText " -> "
  renderExp expr

renderPattern :: EPattern -> RenderM ()
renderPattern (EVarP x) = renderText x
renderPattern (ELitP x) = renderLiteral x
renderPattern EWildP = renderText "_"
renderPattern (EConsP name patterns) = do
  renderText name
  renderSpace
  renderIC (renderSpace) patterns renderPattern

getIntend :: Int -> Text
getIntend x = T.replicate x $ " "

renderCon :: ECons -> RenderM ()
renderCon (ERecord cname fds) = do
  renderText cname
  renderText " { "
  renderIC (renderText ", ") fds (renderText.renderNamedField)
  renderText " } "
renderCon (EProduct cname fds) = do
  renderText cname
  renderSpace
  renderIC (renderText " ") (getRenderedName <$> fds) renderText
renderCon (ESum cons_) = renderIC (renderText " | ") cons_ renderCon
renderCon (ENullary con) = renderText con
renderCon EEmpty = renderText ""

-- | Elm code gen
type TArg = Text

type FArg = Text

type FSig = Maybe Text

data ElmSrc = ElmSrc [EDec]

data EDec
  = EFunc Text FSig [FArg] EExpr
  | EType Text [TArg] ECons
  deriving (Show, Eq)

data ECons
  = ERecord Text [ENamedField]
  | EProduct Text [TypeDescriptor]
  | ESum [ECons]
  | ENullary Text
  | EEmpty
  deriving (Show, Eq)

type ENamedField
  = (Text, TypeDescriptor)

data EExpr
  = ECase EExpr [ECaseBranch]
  | EFuncApp EExpr EExpr
  | EInlineApp EExpr EExpr EExpr
  | EName Text
  | EList [EExpr]
  | ELiteral ELit
  | ETuple [EExpr]
  | ELet [EDec] EExpr
  | ERec [EField]
  deriving (Eq, Show)

instance IsString EExpr where
  fromString = (EName).pack
  

type EField = (Text, EExpr)

type EBinding
  = (EPattern, EExpr)

data ELit
  = EStringL String
  | EIntL Int
  deriving (Eq, Show)

type ECaseBranch
  = (EPattern, EExpr)

data EPattern
  = EVarP Text
  | EConsP Text [EPattern]
  | ELitP ELit
  | EWildP
  deriving (Eq, Show)

data DefConfig
  = GenerateDefPoly MData
  | GenerateDefSimple MData
  | GenerateEncDec MData
  | GenerateAll MData
  | GenerateAllPoly MData
  deriving (Show)

type GenConfig
  = DMS.Map MData [(DefConfig, HType)]

type SConfig = State GenConfig ()

type HTypeTxt = HType_ MyT
type HFieldTxt = HField_ MyT
type HConstructorTxt = HConstructor_ MyT

data ElmVersion = Elm18 | Elm19

data TypeDescriptor
  = Concrete CTData
  | Polymorphic [Text] CTData
  | List TypeDescriptor Text
  | TDMaybe TypeDescriptor Text
  | Primitive Text Text
  | TRecusrive MData
  deriving (Show, Eq)

data CTData
  = CTData Text Text Constructors
  | CTEmpty Text Text
  deriving (Show, Eq)

data Constructors
  = SingleConstructor ConstructorDescriptor
  | ManyConstructors (NE.NonEmpty ConstructorDescriptor)
  deriving (Show, Eq)

data ConstructorDescriptor
  = RecordConstructor Text (Fields NamedField)
  | SimpleConstructor Text (Fields TypeDescriptor)
  | NullaryConstructor Text
  deriving (Show, Eq)

data Fields a
  = SingleField a
  | ManyFields (NE.NonEmpty a)
  deriving (Show, Eq)

data NamedField
  = NamedField Text TypeDescriptor
  deriving (Show, Eq)

getCTDName :: CTData -> Text
getCTDName (CTData a _ _) = a
getCTDName _ = error "Unimpl"

renderNamedField :: ENamedField -> Text
renderNamedField (name, td) = T.concat [ name, " : ", getRenderedName td]

convertHField :: HField -> ReaderT GenConfig Q HFieldTxt
convertHField (HField a t) = do
  b <- deriveType t
  pure $ HField a b

convertHCon :: HConstructor -> ReaderT GenConfig Q HConstructorTxt
convertHCon (HConstructor a b) = do
  fields <- mapM convertHField b
  pure $ HConstructor a fields

-- | Takes an HTypeText, refies the corresponding
-- type using template haskell, and inserts type arguments
-- from the original type into the corresponding types in the
-- constructor fields, replacing the concrete types there.
--
mkPolyMorphic :: HTypeTxt -> LibM HTypeTxt
mkPolyMorphic _htype@(HType (MData tnString a b _) hcons _) = do
  mtName <- R.lift $ lookupTypeName $ unpack tnString
  case mtName of
    Just tName -> do
      info <- R.lift $ reify tName
      let tArgs = getTypeArgs info
      pure $ HType
        (MData tnString a b $ Just tArgs)
        (Prelude.foldr
          (mkPolyMorphicConstructor (getConstructors info))
          hcons
          tArgs)
        (mkMyT $ MyT <$> tArgs)
    Nothing -> error $ unpack $ T.concat ["Cannot find type with name ", tnString, " in scope"]
  where
    mkPolyMorphicConstructor :: [Con] -> Name -> [HConstructorTxt] -> [HConstructorTxt]
    mkPolyMorphicConstructor cons_ tvName hcons_ =
        DL.zipWith (mkPolyMorphicConstructor_ tvName) hcons_ cons_
      where
      mkPolyMorphicConstructor_ :: Name -> HConstructorTxt -> Con -> HConstructorTxt
      mkPolyMorphicConstructor_ tvName_ (HConstructor cn fields) con =
       HConstructor cn $
         DL.zipWith
           (mkPolyMorphicField tvName_)
           fields
           (getConstructorFields con)
    mkPolyMorphicField :: Name -> HFieldTxt -> Type -> HFieldTxt
    mkPolyMorphicField tvName (HField fn ht) t = HField fn (insertTVar tvName ht t)
    insertTVar :: Name -> HTypeTxt -> Type -> HTypeTxt
    insertTVar tvName (HType md hc mt) t = HType md hc $ insertTVar_ tvName mt t
    insertTVar tvName (HPrimitive md mt) t = HPrimitive md $ insertTVar_ tvName mt t
    insertTVar tvName (HList ht) (AppT ListT t) = HList (insertTVar tvName ht t)
    insertTVar tvName (HMaybe md ht) (AppT _ t) = HMaybe md (insertTVar tvName ht t)
    insertTVar _ (HTypeVar a_) _ = HTypeVar a_
    insertTVar _ (HRecursive md) _ = HRecursive md
    insertTVar _ _ _ = error "Not implemented"
    insertTVar_ :: Name -> MyT -> Type -> MyT
    insertTVar_ tvName myt (VarT n) =
      if tvName == n then MyT tvName
        else myt
    insertTVar_ _ myt (ConT _) = myt
    insertTVar_ tvName (MyAppT m1 m2) (AppT t1 t2) = MyAppT (insertTVar_ tvName m1 t1) (insertTVar_ tvName m2 t2)
    insertTVar_ _ a1 _ = a1
    getConstructorFields :: Con -> [Type]
    getConstructorFields c =
      case c of
        (NormalC _ args) -> snd <$> args
        (RecC _ args) -> (\(_, _, x) -> x) <$> args
        _ -> error "Not implemented"
mkPolyMorphic _ = error "Not implemented"

deriveType :: HType -> LibM HTypeTxt
deriveType htype@(HType (MData _ _ _ _) _ _) = do
  ta <- getConcreteTypeArgs htype
  let HType a b _ = htype in do
    consts <- mapM convertHCon b
    pure $ HType a consts ta
deriveType (HPrimitive (MData tnString a b c) _) = pure (HPrimitive (MData tnString a b c) (MyT $ mkName $ unpack $ tnString))
deriveType (HList a) = do
  htt <- deriveType a
  pure $ HList htt
deriveType (HMaybe md a) = do
  htt <- deriveType a
  pure $ HMaybe md htt
deriveType (HRecursive mdata) = pure (HRecursive mdata)
deriveType _ = error "Unimplemented"

dropPackagePrefix :: String -> String
dropPackagePrefix x = DL.reverse $ DL.takeWhile (/= '.') $ DL.reverse x

data MyT = MyEmpty | MyAppT MyT MyT | MyT Name deriving (Show)

mkMyT :: [MyT] -> MyT
mkMyT [] = MyEmpty
mkMyT (x:xs) = DL.foldl (\a i -> MyAppT a i) x xs

myTtoText :: MyT -> Bool -> Text
myTtoText myt wp = if isTuple myt then formatTuple myt else myTtoText' myt wp
  where
  myTtoText' :: MyT -> Bool -> Text
  myTtoText' (MyT name) _ = T.strip $ pack $ nameToText name
  myTtoText' (MyAppT t1 MyEmpty) True = myTtoText t1 False
  myTtoText' (MyAppT t1 t2) True = T.concat ["(", myTtoText t1 False, " ", myTtoText t2 True, ")"]
  myTtoText' (MyAppT t1 t2) False = T.concat [myTtoText t1 False, " ", myTtoText t2 True]
  myTtoText' MyEmpty _ = ""
  formatTuple :: MyT -> Text
  formatTuple myt_ = T.concat ["(", T.intercalate "," $ DL.reverse $ formatTuple' myt_, ")"]
    where
    formatTuple' :: MyT -> [Text]
    formatTuple' (MyT _) = []
    formatTuple' MyEmpty = []
    formatTuple' (MyAppT t1 t2) = (myTtoText t2 True):(formatTuple' t1)
  isTuple :: MyT -> Bool
  isTuple (MyT name) =
    case (nameToText name) of
      [] -> False
      (c:_) -> c == '('
  isTuple MyEmpty = False
  isTuple (MyAppT t1 _) = isTuple t1

getConcreteTypeArgs :: HType -> LibM MyT
getConcreteTypeArgs (HType (MData tnString _ _ _) htcons _) = do
  info <- getInfo $ unpack tnString
  tArgs <- mapM (lookupTypeArg info) (getTypeArgs info)
  pure $ mkMyT ((MyT $ mkName $ unpack $ tnString) : tArgs)
  where
    lookupTypeArg :: Info -> Name -> LibM MyT
    lookupTypeArg info tvName = do
      let (ahType, aType) = getTypeInfo getConstructorField
      cTypes <- getConcreteTypeArgs ahType
      pure $ unwrapBoth cTypes aType
      where
        unwrapBoth :: MyT -> Type -> MyT
        unwrapBoth mt (VarT tname) = if tname == tvName then mt else error "Type lookup failed"
        unwrapBoth (MyAppT mt1 mt2) (AppT t1 t2) =
          if lookInType t1 then unwrapBoth mt1 t1 else unwrapBoth mt2 t2
          where
            lookInType :: Type -> Bool
            lookInType (AppT t1_ t2_) = if lookInType t1_ then True else lookInType t2_
            lookInType (ConT _) = False
            lookInType (VarT n) = n == tvName
            lookInType _  = error "Unimplemented"
        unwrapBoth a@(MyT _) _ = a
        unwrapBoth a@(MyEmpty) _ = a
        unwrapBoth _ _ = error "Unimplemented"
        getConstructorField :: (Name, Int)
        getConstructorField =
          case catMaybes $ lookInConstructor <$> (getConstructors info) of
            (a:_) -> a
            _ -> error ("Constructor lookup failed for type var " ++ show tvName)
            where
              lookInConstructor :: Con -> Maybe (Name, Int)
              lookInConstructor c = let
                (cname, cargs) = getConstructorInfo c
                in case DL.filter isJust $ DL.zipWith lookInType cargs [0..] of
                  ((Just x):_) -> Just (cname, x)
                  _ -> Nothing
                where
                lookInType :: Type -> Int -> Maybe Int
                lookInType (VarT x) idx = if x == tvName then Just idx else Nothing
                lookInType (AppT t1 t2) idx =
                  case lookInType t2 idx of
                    Just a -> Just a
                    Nothing -> lookInType t1 idx
                lookInType _ _ = Nothing
        getConstructorInfo :: Con -> (Name, [Type])
        getConstructorInfo c =
          case c of
            (NormalC n args) -> (n, snd <$> args)
            (RecC n args) -> (n, (\(_, _, x) -> x) <$> args)
            x -> error ("Unsupported constructor given to fetch info" ++ show x)
        getTypeInfo :: (Name, Int) -> (HType, Type)
        getTypeInfo (cName, fIdx) =
          case DL.find findFn htcons of
            Just (HConstructor (CName _) fields) ->
              let HField _ htype = fields !! fIdx in (htype, getTHType)
            Nothing -> error "Constructor not found in htype"
          where
            findFn :: HConstructor -> Bool
            findFn (HConstructor (CName x) _) = unpack x == nameToText cName
            getTHType :: Type
            getTHType =
              case DL.find findFn2 (getConstructors info) of
                Just con ->
                  let (_, fields) = getConstructorInfo con in fields !! fIdx
                Nothing -> error "Unimplemented"
              where
                findFn2 :: Con -> Bool
                findFn2 c = let (x, _) = getConstructorInfo c in cName == x
    getInfo :: String -> LibM Info
    getInfo tName = do
      mtName <- R.lift $ lookupTypeName tName
      case mtName of
        Just tName_ -> do
          R.lift $ reify tName_
        Nothing -> do -- To make tuples work
          R.lift $ reify $ mkName tName
getConcreteTypeArgs (HPrimitive md _) = pure $ MyT $ mkName $ unpack $  _mTypeName md
getConcreteTypeArgs (HList ht) = do
  x <- getConcreteTypeArgs ht
  pure $ MyAppT (MyT $ mkName "List") x 
getConcreteTypeArgs (HMaybe _ ht) = do
  x <- getConcreteTypeArgs ht
  pure $ MyAppT (MyT $ mkName "Maybe") x 
getConcreteTypeArgs (HRecursive md) = pure $ MyT $ mkName $ unpack $ _mTypeName md
getConcreteTypeArgs _ = error "Unimplemented"

extractMd :: HType_ a -> MData
extractMd (HType md _ _ )= md
extractMd (HMaybe md _) = md
extractMd (HList _)= error "Meta data not available"
extractMd (HPrimitive md _ )= md
extractMd (HTypeVar _)= error "Meta data not available"
extractMd (HRecursive md)= md

getConstructors :: Info -> [Con]
getConstructors info =
  case info of
    TyConI (DataD [] _ _ _ c _) -> c
    _ -> error "Unsupported type info"

getTypeArgs :: Info -> [Name]
getTypeArgs (TyConI (DataD _ _ args _ _ _)) = mapFn <$> args
  where
    mapFn :: TyVarBndr -> Name
    mapFn (PlainTV n) = n
    mapFn (KindedTV n _) = n
getTypeArgs _ = error "Unimplemented"

nameToText :: Name -> String
nameToText (Name (OccName a) _) = a

httToName :: HTypeTxt -> Text
httToName (HType _ _ t) = myTtoText t True
httToName (HPrimitive _ t) = myTtoText t True
httToName (HList t) = T.concat ["(List ", httToName t, ")"]
httToName (HTypeVar t) = t
httToName (HMaybe _ ht) = T.concat ["(Maybe ", httToName ht, ")"]
httToName (HRecursive md) = _mTypeName md

toTypeDescriptor :: HTypeTxt -> TypeDescriptor
toTypeDescriptor ht@(HType (MData tnString _ _ (Just (ta@(_:_)))) x _) = 
  Polymorphic (pack.nameToText <$> ta) $
    case x of
      [] -> CTEmpty tnString (httToName ht)
      (a:as) -> CTData tnString (httToName ht) $ toConstructors (a:|as)
toTypeDescriptor ht@(HType (MData tnString _ _ Nothing) x _) =
  Concrete $
    case x of 
      [] -> CTEmpty tnString (httToName ht)
      (a:as) -> CTData tnString (httToName ht) $ toConstructors (a:|as)
toTypeDescriptor ht@(HPrimitive (MData tnString _ _ _) _) = Primitive tnString (httToName ht)
toTypeDescriptor a@(HList t) = List (toTypeDescriptor t) (httToName a)
toTypeDescriptor a@(HMaybe _ t) = TDMaybe (toTypeDescriptor t) (httToName a)
toTypeDescriptor (HRecursive md) = TRecusrive $ md
toTypeDescriptor a = error $ show a

toConstructors :: NE.NonEmpty HConstructorTxt -> Constructors
toConstructors (x :| []) = SingleConstructor (mkConstructorDesc x)
toConstructors (x :| xs) = ManyConstructors $ (mkConstructorDesc x) NE.:| (mkConstructorDesc <$> xs)

mkConstructorDesc :: HConstructorTxt -> ConstructorDescriptor
mkConstructorDesc (HConstructor (CName cname) fs) =
  case fs of
    [] -> NullaryConstructor cname
    (hf@(HField (Just _) _):hfs) -> RecordConstructor cname $ mkRecordFields (hf NE.:| hfs)
    (hf@(HField Nothing _):hfs) -> SimpleConstructor cname $ mkUnNamedFields (hf NE.:| hfs)

mkRecordFields :: NE.NonEmpty HFieldTxt -> Fields NamedField
mkRecordFields (x :| []) = SingleField $ mkRecordField x
mkRecordFields (x :| xs) = ManyFields $ (mkRecordField x) NE.:| (mkRecordField <$> xs)

mkRecordField :: HFieldTxt -> NamedField
mkRecordField (HField (Just x) htype) = NamedField x (toTypeDescriptor htype)
mkRecordField _ = error "Incompatible field to make a named field"

mkUnNamedFields :: NE.NonEmpty HFieldTxt -> Fields TypeDescriptor
mkUnNamedFields (x :| []) = SingleField $ mkUnNamedField x
mkUnNamedFields (x :| xs) = ManyFields $ (mkUnNamedField x) NE.:| (mkUnNamedField <$> xs)

mkUnNamedField :: HFieldTxt -> TypeDescriptor
mkUnNamedField (HField _ htype) = toTypeDescriptor htype

getRenderedName :: TypeDescriptor -> Text
getRenderedName (Concrete c) = getRenderedNameFromCTdata c
getRenderedName (Polymorphic _ c) = getRenderedNameFromCTdata c
getRenderedName (List _ c) = c
getRenderedName (TDMaybe _ c) = c
getRenderedName (Primitive _ c) = c
getRenderedName (TRecusrive md) = _mTypeName md

getRenderedNameFromCTdata :: CTData -> Text
getRenderedNameFromCTdata (CTData _ x _) = x
getRenderedNameFromCTdata (CTEmpty _ x) = x
