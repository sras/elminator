{-# LANGUAGE OverloadedStrings #-}

module Elminator.Elm19 (generateElm, elmFront) where

import Generics.Simple
import Elminator.Lib
import Data.Text as T hiding (zipWith)
import Data.Aeson as Aeson
import qualified Data.List as DL
import qualified Data.List.NonEmpty as NE
import Prelude
import qualified Prelude as P

elmFront :: Text
elmFront = "\
\module Autogen exposing (..)\n\
\\n\
\import Json.Encode as E\n\
\import Json.Decode as D\n\
\\n\
\seqApp : D.Decoder (a1 -> v) -> D.Decoder a1 -> D.Decoder v\n\
\seqApp inDec oDec =\n\
\  let\n\
\    mapFn v = D.map (\\x -> x v) inDec\n\
\  in D.andThen mapFn oDec\n\
\\n\
\encodeMaybe : (a -> E.Value)-> Maybe a -> E.Value\n\
\encodeMaybe fn ma = case ma of\n\
\  Just a -> fn a\n\
\  Nothing -> E.null\n\
\\n\n"

generateElm :: DefConfig -> HType -> Options -> LibM Text
generateElm d h opt = do
  ht <- deriveType h
  case d of
    GenerateDefPoly _ -> do
      htt <- mkPolyMorphic ht
      pure $ renderElm $ ElmSrc [generateElmDef $ toTypeDescriptor htt]
    GenerateDefSimple _ ->
      pure $ renderElm $ ElmSrc [generateElmDef $ toTypeDescriptor ht]
    GenerateEncDec _ -> do
      pure $ renderElm $ ElmSrc
        [ generateEncoder (toTypeDescriptor ht) opt
        , generateDecoder (toTypeDescriptor ht) opt
        ]
    GenerateAll _ -> do
      pure $ renderElm $ ElmSrc
        [ generateElmDef $ toTypeDescriptor ht
        , generateEncoder (toTypeDescriptor ht) opt
        , generateDecoder (toTypeDescriptor ht) opt
        ]
    GenerateAllPoly _ -> do
      htt <- mkPolyMorphic ht
      pure $ renderElm $ ElmSrc
        [ generateElmDef $ toTypeDescriptor htt
        , generateEncoder (toTypeDescriptor ht) opt
        , generateDecoder (toTypeDescriptor ht) opt
        ]

getCTDataName :: CTData -> Text
getCTDataName (CTData n _ _) = n
getCTDataName (CTEmpty _ _) = ""

generateDecoder :: TypeDescriptor -> Options -> EDec
generateDecoder (Concrete ctdata) opts = let
  expr = generateDecoderCtd ctdata opts
  in EFunc
    (T.concat
      [ "decode"
      , getCTDataName ctdata]) 
    (Just $ T.concat ["D.Decoder", " ", getRenderedNameFromCTdata ctdata]) [] $
    expr
generateDecoder _ _ = error "Unim"

generateDecoderCtd :: CTData -> Options -> EExpr
generateDecoderCtd (CTData _ _ crs) opts = decoderToDecoderEExpr (gdConstructor crs opts)
generateDecoderCtd (CTEmpty _ _) _ = error "No value to decode"

gdConstructor :: Constructors -> Options -> Decoder
gdConstructor (SingleConstructor cd) opts =
  if tagSingleConstructors opts
    then gdTaggedWithConstructor [cd] opts
    else DUntagged $ [(getCName cd, mkContentDecoder cd opts)]
gdConstructor (ManyConstructors cds) opts =
  gdTaggedWithConstructor (NE.toList cds) opts

gdTaggedWithConstructor :: [ConstructorDescriptor] -> Options -> Decoder
gdTaggedWithConstructor cds opts =
  case sumEncoding opts of
    TaggedObject tfn cfn ->
        DTagged (pack tfn) (pack cfn) cdPair
    ObjectWithSingleField -> DUnderConKey cdPair
    TwoElemArray -> DTwoElement cdPair
    UntaggedValue -> DUntagged $ (\cd -> (getCName cd, mkContentDecoder cd opts)) <$> cds
  where
    cdPair :: [(ConName, ConTag, ContentDecoder)]
    cdPair = (\cd -> (getCName cd, pack $ constructorTagModifier opts $ unpack $ getCName cd, mkContentDecoder cd opts)) <$> cds

mkContentDecoder :: ConstructorDescriptor -> Options -> ContentDecoder
mkContentDecoder cd opts =
  case cd of
    RecordConstructor _cname (SingleField nf) ->
      if unwrapUnaryRecords opts
        then case sumEncoding opts of
          ObjectWithSingleField -> CDRecordRaw $ modifyFieldLabel nf
          TwoElemArray -> CDRecordRaw $ modifyFieldLabel nf
          UntaggedValue -> CDRecordRaw $ modifyFieldLabel nf
          TaggedObject _ _ -> CDRecord [modifyFieldLabel nf]
        else CDRecord [modifyFieldLabel nf]
    RecordConstructor _cname (ManyFields nf) -> CDRecord $ NE.toList $ NE.map modifyFieldLabel nf
    SimpleConstructor _cname (SingleField f) -> CDRaw f
    SimpleConstructor _cname (ManyFields f) -> CDList $ NE.toList $ f
    NullaryConstructor _ -> CDEmpty
  where
    modifyFieldLabel :: NamedField -> (FieldName, FieldTag, TypeDescriptor)
    modifyFieldLabel (NamedField a b) = (a, pack $ fieldLabelModifier opts $ unpack $ a, b)

firstOf3 :: (a, b, c) -> a
firstOf3 (a, _, _) = a

prependMk :: Text -> Text
prependMk x = T.concat ["mk", x]

decoderToDecoderEExpr :: Decoder -> EExpr
decoderToDecoderEExpr d =
  case d of
    DUnderConKey cds ->
      EFuncApp "D.oneOf" (EList $ zipWith decodeUnderConKey cds ((prependMk.firstOf3) <$> cds))
    DTagged tfn cfn cds -> let
      expr = EFuncApp
        (EFuncApp "D.andThen" "tryCons")
        (EFuncApp (EFuncApp "D.field" (ELiteral $ EStringL $ unpack tfn)) "D.string")
      in ELet [mkTryCons (Just cfn) cds] expr
    DTwoElement cds -> let
      expr = EFuncApp
        (EFuncApp "D.andThen" (EInlineApp ">>" "tryCons" (EFuncApp "D.index" (ELiteral $ EIntL 1))))
        (EFuncApp (EFuncApp "D.index" (ELiteral $ EIntL 0)) "D.string")
      in ELet [mkTryCons Nothing cds] expr
    DUntagged cds -> 
      EFuncApp "D.oneOf" (EList $ (\(cname, cd) -> contentDecoderToExp Nothing cname cd) <$> cds)
      
mkTryCons :: Maybe Text -> [(ConName, ConTag, ContentDecoder)] -> EDec
mkTryCons mcntFname cds =
  EFunc "tryCons" Nothing ["v"] $ ECase "v" ((fn1 <$> cds) ++ [emptyPattern])
  where
  emptyPattern = (EWildP, EFuncApp "D.fail" (ELiteral $ EStringL "None of the constructors match"))
  fn1 :: (ConName, ConTag, ContentDecoder) -> ECaseBranch
  fn1 (cname, ctag, cd) = let
    pattern = ELitP (EStringL $ unpack $ ctag)
    expression = contentDecoderToExp mcntFname cname cd
    in (pattern, expression)

decodeUnderConKey :: (ConName, ConTag, ContentDecoder) -> Text -> EExpr
decodeUnderConKey (cname, ctag, cd) _ =
  EFuncApp
    (EFuncApp "D.field" (ELiteral $ EStringL $ unpack $ ctag)) $
    contentDecoderToExp Nothing cname cd

contentDecoderToExp :: Maybe Text -> ConName -> ContentDecoder -> EExpr
contentDecoderToExp mcntFname cname cd =
   case cd of
     CDRecord nfds -> let
       makerFnName = (prependMk cname)
       makerFn = mkRecorderMaker makerFnName cname nfds
       in ELet [makerFn] $ aggregateDecoders makerFnName $ mapFn <$> nfds
     CDRecordRaw nfd@(_, _, td) -> let
       makerFnName = (prependMk cname)
       makerFn = mkRecorderMaker makerFnName cname [nfd]
       in ELet [makerFn] $ aggregateDecoders makerFnName [getDecoderName td]
     CDList tds -> let
       agg = aggregateDecoders cname $ zipWith zipFn [0..] tds
       in case mcntFname of
         Just cntFname -> EFuncApp (EFuncApp "D.field" (ELiteral $ EStringL $ unpack cntFname)) agg
         Nothing -> agg
     CDRaw td -> let
       agg = aggregateDecoders cname [getDecoderName td]
       in case mcntFname of
         Just cntFname -> EFuncApp (EFuncApp "D.field" (ELiteral $ EStringL $ unpack cntFname)) agg
         Nothing -> agg
     CDEmpty -> error "Cannot decode empty"
  where
    mapFn :: (FieldName, FieldTag, TypeDescriptor) -> EExpr
    mapFn (_, ft, td) = case td of
      TDMaybe wtd _ -> EFuncApp "D.maybe" (EFuncApp (EFuncApp "D.field" (ELiteral $ EStringL $ unpack ft)) (getDecoderName wtd))
      _ -> EFuncApp (EFuncApp "D.field" (ELiteral $ EStringL $ unpack ft)) (getDecoderName td)
    zipFn :: Int -> TypeDescriptor -> EExpr
    zipFn idx td = EFuncApp (EFuncApp "D.index" (ELiteral $ EIntL idx)) (getDecoderName td)

aggregateDecoders :: Text -> [EExpr] -> EExpr
aggregateDecoders mfn exprs = let
  fieldCount = P.length exprs
  field8 = DL.take 8 exprs
  field8L = P.length field8
  decU8 = DL.foldl' EFuncApp (EFuncApp (EName $ T.concat ["D.map", if field8L >1 then pack $ show field8L else ""]) (EName mfn)) $ field8
  in if fieldCount < 9
    then decU8 
    else DL.foldl' (\a v -> EFuncApp ((EFuncApp "seqApp") a) v) decU8 $ DL.drop 8 exprs

mkRecorderMaker :: Text -> ConName -> [(FieldName, FieldTag, TypeDescriptor)]  -> EDec
mkRecorderMaker rmName cname fds = let
  args = 
    zipWith
      (\_ y -> T.concat ["a", pack $ show y])
      fds
      [(1::Int)..]
  in EFunc rmName Nothing args $
    EFuncApp (EName cname) (ERec $ zipWith mkField fds args)
  where
    mkField :: (FieldName, FieldTag, TypeDescriptor) -> Text -> EField
    mkField (fn, _, _) a = (fn, EName a)

getCName :: ConstructorDescriptor -> Text
getCName (RecordConstructor x _) = x
getCName (SimpleConstructor x _) = x
getCName (NullaryConstructor x) = x

generateEncoder :: TypeDescriptor -> Options -> EDec
generateEncoder (Concrete ctdata) opts =
  EFunc
    (T.concat
      [ "encode"
      , getCTDataName ctdata]) 
    (Just $ T.concat [getRenderedNameFromCTdata ctdata, " -> ", "E.Value"])
    ["a"] $
    generateEncoderCtd ctdata opts
generateEncoder (Polymorphic _ _) _ = error "Cannot create encoder for polymorphic type"
generateEncoder _ _ = error "Unim"

generateEncoderCtd :: CTData -> Options -> EExpr
generateEncoderCtd (CTData _ _ crs) opts = decoderToEncoderEExpr $ gdConstructor crs opts
generateEncoderCtd (CTEmpty _ _) _ = error "No value to encode"

decoderToEncoderEExpr :: Decoder -> EExpr
decoderToEncoderEExpr d = case d of
  DUnderConKey cons_ ->
    ECase "a" $ mapFn <$> cons_
  DTagged tfn cfn cons_ ->
    ECase "a" $ mapFn2 tfn cfn <$> cons_
  DTwoElement cons_ ->
    ECase "a" $ mapFn3 <$> cons_
  DUntagged cons_ ->
    ECase "a" $ mapFn4 <$> cons_
  where
  mapFn4 :: (ConName, ContentDecoder) -> ECaseBranch
  mapFn4 (cname, cd) = (makePattern (cname, "", cd), contentDecoderToEncoderExp Nothing cd)
  mapFn3 :: (ConName, ConTag, ContentDecoder) -> ECaseBranch
  mapFn3 a@(_, ctag, cd) =
    ( makePattern a
    , EFuncApp (EFuncApp "E.list" "identity") $ EList [EFuncApp "E.string" $ ELiteral $ EStringL $ unpack $ ctag, contentDecoderToEncoderExp Nothing cd])
  mapFn2 :: Text -> Text -> (ConName, ConTag, ContentDecoder) -> ECaseBranch
  mapFn2 tfn cfn a = (makePattern a, encoderTagged tfn cfn a)
  mapFn :: (ConName, ConTag, ContentDecoder) -> ECaseBranch
  mapFn a = (makePattern a, encoderUnderConKey a)
  makePattern :: (ConName, ConTag, ContentDecoder) -> EPattern
  makePattern (cname, _, cd) = case cd of
    CDRecord _ -> EConsP cname $ [EVarP "x"]
    CDRecordRaw _ -> EConsP cname $ [EVarP "x"]
    CDList tds -> EConsP cname $
      zipWith
        (\x _ -> EVarP $ T.concat ["a", pack $ show x])
        [(1::Int)..]
        tds
    CDRaw _ -> EConsP cname [EVarP "a1"]
    CDEmpty -> EConsP cname []

encoderUnderConKey :: (ConName, ConTag, ContentDecoder) -> EExpr
encoderUnderConKey (_, ctag, cd) =
  EFuncApp "E.object" $
    EList [ETuple [ELiteral $ EStringL $ unpack ctag, contentDecoderToEncoderExp Nothing cd]]

encoderTagged :: Text -> Text -> (ConName, ConTag, ContentDecoder) -> EExpr
encoderTagged tfn cfn (_, ctag, cd) = case cd of
  CDRecord _ -> contentDecoderToEncoderExp (Just (tfn, ctag)) cd
  CDRecordRaw _ -> contentDecoderToEncoderExp Nothing cd
  _ -> 
    EFuncApp "E.object" $ EList $ 
      [ ETuple [ELiteral $ EStringL $ unpack $ tfn, EFuncApp "E.string" $ ELiteral $ EStringL $ unpack $ ctag]
      , ETuple [ELiteral $ EStringL $ unpack $ cfn, contentDecoderToEncoderExp Nothing cd]
      ]

contentDecoderToEncoderExp :: Maybe (FieldName, ConTag) -> ContentDecoder -> EExpr
contentDecoderToEncoderExp mct cd = case cd of
  CDRecord fds ->
    EFuncApp "E.object" $
      case mct of
        Nothing -> EList $ (mapFn <$> fds)
        Just (tn, ctag) -> let
          x = (ETuple [ELiteral $ EStringL $ unpack tn, EFuncApp "E.string" $  ELiteral $ EStringL $ unpack $ ctag ])
          in EList $ x:(mapFn <$> fds)
  CDRecordRaw (fn, _, td) ->
    EFuncApp (getEncoderName td) $
      EName $ T.concat ["x",".",fn]
  CDList tds ->
    EFuncApp (EFuncApp "E.list" "identity") $
      EList $ zipWith zipFn tds [1..]
  CDRaw td ->
    EFuncApp (getEncoderName td) "a1"
  CDEmpty -> EFuncApp (EFuncApp "E.list" "identity") $ EList []
  where
  zipFn :: TypeDescriptor -> Int -> EExpr
  zipFn td idx = EFuncApp (getEncoderName td) $ EName $ T.concat ["a", pack $ show idx]
  mapFn :: (FieldName, FieldTag, TypeDescriptor) -> EExpr
  mapFn (fn, ft, td) =
    ETuple
      [ ELiteral $ EStringL $ unpack ft
      , EFuncApp (getEncoderName td) $
          EName $ T.concat ["x",".",fn]]

getEncoderName :: TypeDescriptor -> EExpr
getEncoderName (Concrete ctd) = EName $ T.concat ["encode", getCTDName ctd]
getEncoderName (Polymorphic _ ctd) = EName $ T.concat ["encode", getCTDName ctd]
getEncoderName (Primitive n _) = EName $ getPrimitiveEncoder n
getEncoderName (List x _) = (EFuncApp "E.list" (getEncoderName x))
getEncoderName (TDMaybe x _) = (EFuncApp "encodeMaybe" (getEncoderName x))
getEncoderName (TRecusrive md) = EName $ T.concat ["encode", _mTypeName md]

getDecoderName :: TypeDescriptor -> EExpr
getDecoderName (Concrete ctd) = EName $ T.concat ["decode", getCTDName ctd]
getDecoderName (Polymorphic _ ctd) = EName $ T.concat ["decode", getCTDName ctd]
getDecoderName (Primitive n _) = EName $ getPrimitiveDecoder n
getDecoderName (List x _) = EFuncApp (EName "D.list") (getDecoderName x)
getDecoderName (TRecusrive md) = EName $ T.concat ["decode", _mTypeName md]
getDecoderName (TDMaybe x _) = (EFuncApp "D.maybe" (getDecoderName x))

getPrimitiveDecoder :: Text -> Text
getPrimitiveDecoder "String" = "D.string"
getPrimitiveDecoder "Int" = "D.int"
getPrimitiveDecoder "Float" = "D.float"
getPrimitiveDecoder "Bool" = "D.bool"
getPrimitiveDecoder s = T.concat ["encode", s]

getPrimitiveEncoder :: Text -> Text
getPrimitiveEncoder "String" = "E.string"
getPrimitiveEncoder "Int" = "E.int"
getPrimitiveEncoder "Float" = "E.float"
getPrimitiveEncoder "Bool" = "E.bool"
getPrimitiveEncoder s = T.concat ["encode", s]

-- | Generate Elm type definitions
generateElmDef :: TypeDescriptor -> EDec
generateElmDef (Concrete (CTData tname _ c))
  = EType tname [] $ generateElmDefC c
generateElmDef (Concrete (CTEmpty tname _))
  = EType tname [] EEmpty
generateElmDef (Polymorphic targs (CTData tname _ c))
  = EType tname targs $ generateElmDefC c
generateElmDef (Polymorphic targs (CTEmpty tname _))
  = EType tname targs EEmpty
generateElmDef _
  = error "Not implemented"

generateElmDefC :: Constructors -> ECons
generateElmDefC (SingleConstructor cd) = generateElmDefCD cd
generateElmDefC (ManyConstructors cdl) = ESum $ NE.toList $ NE.map generateElmDefCD cdl

generateElmDefCD :: ConstructorDescriptor -> ECons
generateElmDefCD (RecordConstructor cname nfs)
  = ERecord cname $ generateRecordFields nfs
generateElmDefCD (SimpleConstructor cname fs)
  = EProduct cname $ generateUnNamedFields fs
generateElmDefCD (NullaryConstructor cname)
  = ENullary cname

generateRecordFields :: Fields NamedField -> [ENamedField]
generateRecordFields (SingleField (NamedField a b)) = [(a, b)]
generateRecordFields (ManyFields n) =
  NE.toList $ NE.map (\(NamedField a b) -> (a, b)) n

generateUnNamedFields :: Fields TypeDescriptor -> [TypeDescriptor]
generateUnNamedFields (SingleField a) = [a]
generateUnNamedFields (ManyFields a) = NE.toList a
