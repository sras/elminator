{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module Elminator.Lib where

import Generics.Simple
import Data.Text as T hiding (foldr)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import qualified Data.List as DL
import qualified Data.Map.Strict as DMS
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
  renderText "type"
  renderSpace
  renderText name 
  if DL.length targs > 0 then renderSpace  else pure ()
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

data ElmVersion = Elm18 | Elm19

data TypeDescriptor
  = Concrete CTData
  | Polymorphic [Name] CTData
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

-- | Takes an HType, refies the corresponding
-- type using template haskell, and inserts type arguments
-- from the original type into the corresponding types in the
-- constructor fields, replacing the concrete types there.
--
mkPolyMorphic :: HType -> LibM HType
mkPolyMorphic _htype@(HUDef (UDefData (MData tnString a b) targs _ hcons)) = do
  mtName <- R.lift $ lookupTypeName $ unpack tnString
  case mtName of
    Just tName -> do
      info <- R.lift $ reify tName
      let tVars = getTypeArgs info
      pure $ HUDef $ UDefData
        (MData tnString a b)
        targs
        (Just tVars)
        (foldr
          (mkPolyMorphicConstructor (getConstructors info))
          hcons
          tVars)
    Nothing -> error $ unpack $ T.concat ["Cannot find type with name ", tnString, " in scope"]
  where
    mkPolyMorphicConstructor :: [Con] -> Name -> [HConstructor] -> [HConstructor]
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
      mkPolyMorphicField _tvName (HField fn ht) t = HField fn (insertTVar tvName ht t)
      insertTVar :: Name -> HType -> Type -> HType
      insertTVar tvname h (VarT n) =
        if n == tvname
          then (HTypeVar n)
          else h
      insertTVar tvname (HUDef udefd) typ = let
        taList = DL.reverse $ udefdTypeArgs udefd
        in HUDef $ udefd { udefdTypeArgs = DL.reverse $ insertTVar_ taList typ }
        where
          insertTVar_ :: [HType] -> Type -> [HType]
          insertTVar_ (h:hs) (AppT t1 t2) =
            (insertTVar tvname h t2):(insertTVar_ hs t1)
          insertTVar_ hs _ =  hs
      insertTVar tvname (HList ht) (AppT ListT t) = HList (insertTVar tvname ht t)
      insertTVar tvname (HMaybe ht) (AppT _ t) = HMaybe (insertTVar tvname ht t)
      insertTVar _ x _ = x
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
    _ -> error "Unsupported type info"

extractMd :: HType -> MData
extractMd (HUDef (UDefData md  _ _ _))= md
extractMd (HMaybe _) = MData "Maybe" "" ""
extractMd (HList _)= error "Meta data not available"
extractMd (HPrimitive md)= md
extractMd (HTypeVar _)= error "Meta data not available"
extractMd (HRecursive md)= md

getTypeArgs :: Info -> [Name]
getTypeArgs (TyConI (DataD _ _ args _ _ _)) = mapFn <$> args
  where
    mapFn :: TyVarBndr -> Name
    mapFn (PlainTV n) = n
    mapFn (KindedTV n _) = n
getTypeArgs _ = error "Unimplemented"

nameToText :: Name -> String
nameToText (Name (OccName a) _) = a

renderHType :: HType -> Text
renderHType htype = renderHType_ htype True

renderHType_ :: HType -> Bool -> Text
renderHType_ h@(HUDef u) ip = 
  if ip
    then if DL.length (udefdTypeArgs u )> 0
      then T.concat ["(", renderHType_ h False, ")"]
      else renderHType_ h False
    else T.intercalate " "  $ (_mTypeName $ udefdMdata u):(renderHType <$> udefdTypeArgs u)
renderHType_ (HPrimitive md) _ = _mTypeName md
renderHType_ (HList t) _ = T.concat ["(List ", renderHType_ t True, ")"]
renderHType_ (HTypeVar t) _ = pack $ nameToText t
renderHType_ (HMaybe ht) _ = T.concat ["(Maybe ", renderHType_ ht True, ")"]
renderHType_ (HRecursive md) _ = _mTypeName md

toTypeDescriptor :: HType -> TypeDescriptor
toTypeDescriptor ht@(HUDef (UDefData (MData tnString _ _) (_:_) (Just tv) x)) =
  Polymorphic tv $
    case x of
      [] -> CTEmpty tnString (renderHType ht)
      (a:as) -> CTData tnString (renderHType ht) $ toConstructors (a:|as)
toTypeDescriptor ht@(HUDef (UDefData (MData tnString _ _) _ _ x)) =
  Concrete $
    case x of 
      [] -> CTEmpty tnString (renderHType ht)
      (a:as) -> CTData tnString (renderHType ht) $ toConstructors (a:|as)
toTypeDescriptor ht@(HPrimitive (MData tnString _ _)) = Primitive tnString (renderHType ht)
toTypeDescriptor a@(HList t) = List (toTypeDescriptor t) (renderHType a)
toTypeDescriptor a@(HMaybe t) = TDMaybe (toTypeDescriptor t) (renderHType a)
toTypeDescriptor (HRecursive md) = TRecusrive $ md
toTypeDescriptor a = error $ show a

toConstructors :: NE.NonEmpty HConstructor -> Constructors
toConstructors (x :| []) = SingleConstructor (mkConstructorDesc x)
toConstructors (x :| xs) = ManyConstructors $ (mkConstructorDesc x) NE.:| (mkConstructorDesc <$> xs)

mkConstructorDesc :: HConstructor -> ConstructorDescriptor
mkConstructorDesc (HConstructor (CName cname) fs) =
  case fs of
    [] -> NullaryConstructor cname
    (hf@(HField (Just _) _):hfs) -> RecordConstructor cname $ mkRecordFields (hf NE.:| hfs)
    (hf@(HField Nothing _):hfs) -> SimpleConstructor cname $ mkUnNamedFields (hf NE.:| hfs)

mkRecordFields :: NE.NonEmpty HField -> Fields NamedField
mkRecordFields (x :| []) = SingleField $ mkRecordField x
mkRecordFields (x :| xs) = ManyFields $ (mkRecordField x) NE.:| (mkRecordField <$> xs)

mkRecordField :: HField -> NamedField
mkRecordField (HField (Just x) htype) = NamedField x (toTypeDescriptor htype)
mkRecordField _ = error "Incompatible field to make a named field"

mkUnNamedFields :: NE.NonEmpty HField -> Fields TypeDescriptor
mkUnNamedFields (x :| []) = SingleField $ mkUnNamedField x
mkUnNamedFields (x :| xs) = ManyFields $ (mkUnNamedField x) NE.:| (mkUnNamedField <$> xs)

mkUnNamedField :: HField -> TypeDescriptor
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
