{-# LANGUAGE OverloadedStrings #-}

module Elminator.Elm19
  ( generateElm
  , elmFront
  , typeDescriptorToDecoder
  ) where

import Control.Monad.Reader as R
import Data.Aeson as Aeson
import qualified Data.List as DL
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.Map.Strict as DMS
import Data.Maybe
import Data.Text as T hiding (any, zipWith)
import Elminator.ELM.CodeGen
import Elminator.Generics.Simple
import Elminator.Lib
import Prelude
import qualified Prelude as P

elmFront :: Text -> Text
elmFront imports =
  T.concat
    [ "\
  \module Autogen exposing (..)\n\
  \\n"
    , imports
    , "\n\n"
    , "import Json.Encode as E\n\
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
    ]

generateTupleEncoder :: Int -> [TypeDescriptor] -> EDec
generateTupleEncoder idx types =
  EFunc (T.concat ["encodeTuple", pack $ show idx]) Nothing [tlVar] $
  ELet [EBinding (ETupleP patterns) (EName tlVar)] eexpr
  where
    tlVar = T.concat ["a", pack $ show $ idx, "1"]
    indexVar :: Int -> Text
    indexVar y = T.concat ["b", pack $ show $ idx, "_", pack $ show y]
    varList :: [Text]
    varList = (zipWith (\_ y -> indexVar y) types [1 ..])
    patterns = EVarP <$> varList
    eexpr =
      EFuncApp (EFuncApp "E.list" "identity") $
      EList $
      zipWith
        (\x i -> (EFuncApp (getEncoderExpr (idx + 1) x) (EName $ indexVar i)))
        types
        [1 ..]

generateTupleDecoder :: Int -> [TypeDescriptor] -> EDec
generateTupleDecoder nidx types =
  EFunc (T.concat ["decodeTuple", pack $ show $ nidx]) Nothing [] $
  ELet [mkTupleMaker mktName nidx types] $
  aggregateDecoders mktName $
  zipWith
    (\t idx ->
       EFuncApp (EFuncApp "D.index" (ELiteral $ EIntL idx)) $
       getDecoderExpr (nidx + 1) t)
    types
    [0 ..]
  where
    mktName = T.concat ["mkTuple", pack $ show nidx]

generateElm :: GenOption -> HType -> Options -> LibM Text
generateElm d h opts = do
  let td = toTypeDescriptor h
  case d of
    Definiton Poly -> do
      hp <- mkPolyMorphic h
      let tdp = toTypeDescriptor hp
      collectExtRefs tdp
      def <- generateElmDef tdp
      pure $ renderElm $ ElmSrc [def]
    Definiton Mono -> do
      def <- generateElmDef td
      collectExtRefs td
      pure $ renderElm $ ElmSrc [def]
    EncoderDecoder -> do
      let decoder = typeDescriptorToDecoder opts td
      collectExtRefs td
      encSrc <- generateEncoder (td, decoder)
      decSrc <- generateDecoder (td, decoder)
      pure $ renderElm $ ElmSrc [encSrc, decSrc]
    Everything Mono -> do
      let decoder = typeDescriptorToDecoder opts td
      collectExtRefs td
      def <- generateElmDef td
      encSrc <- generateEncoder (td, decoder)
      decSrc <- generateDecoder (td, decoder)
      pure $ renderElm $ ElmSrc [def, encSrc, decSrc]
    Everything Poly -> do
      hp <- mkPolyMorphic h
      let tdp = toTypeDescriptor hp
          decoder = typeDescriptorToDecoder opts td
      collectExtRefs td
      def <- generateElmDef tdp
      encSrc <- generateEncoder (tdp, decoder)
      decSrc <- generateDecoder (tdp, decoder)
      pure $ renderElm $ ElmSrc [def, encSrc, decSrc]

getCTDataName :: CTData -> Text
getCTDataName (CTData n _) = tnHead n
getCTDataName (CTEmpty n) = tnHead n

generateDecoder :: (TypeDescriptor, Decoder) -> LibM EDec
generateDecoder (td, decoder) = do
  tdisplay <- mkTypeDisplayFromTd td
  pure $
    case td of
      (SimpleType ctdata) -> fn ctdata tdisplay
      (Polymorphic _ ctdata) -> fn ctdata tdisplay
      _ -> error "Encoders/decoders can only be made for user defined types"
  where
    fn :: CTData -> TypeDisplay -> EDec
    fn ctdata tdisp =
      EFunc
        (T.concat ["decode", getCTDataName ctdata])
        (Just $
         T.concat
           [ "D.Decoder"
           , " "
           , let TypeDisplay x = tdisp
              in x
           ])
        [] $
      decoderToDecoderEExpr decoder

firstOf3 :: (a, b, c) -> a
firstOf3 (a, _, _) = a

prependMk :: Text -> Text
prependMk x = T.concat ["mk", x]

decoderToDecoderEExpr :: Decoder -> EExpr
decoderToDecoderEExpr d =
  case d of
    DUnderConKey cds ->
      EFuncApp
        "D.oneOf"
        (EList $ zipWith decodeUnderConKey cds ((prependMk . firstOf3) <$> cds))
    DTagged tfn cfn cds ->
      let expr =
            EFuncApp
              (EFuncApp "D.andThen" "tryCons")
              (EFuncApp
                 (EFuncApp "D.field" (ELiteral $ EStringL $ unpack tfn))
                 "D.string")
       in ELet [mkTryCons (Just cfn) cds] expr
    DTwoElement cds ->
      let expr =
            EFuncApp
              (EFuncApp
                 "D.andThen"
                 (EInlineApp
                    ">>"
                    "tryCons"
                    (EFuncApp "D.index" (ELiteral $ EIntL 1))))
              (EFuncApp (EFuncApp "D.index" (ELiteral $ EIntL 0)) "D.string")
       in ELet [mkTryCons Nothing cds] expr
    DUntagged cds ->
      EFuncApp
        "D.oneOf"
        (EList $ (\(cname, cd) -> contentDecoderToExp Nothing cname cd) <$> cds)

mkTryCons :: Maybe Text -> [(ConName, ConTag, ContentDecoder)] -> EDec
mkTryCons mcntFname cds =
  EFunc "tryCons" Nothing ["v"] $ ECase "v" ((fn1 <$> cds) ++ [emptyPattern])
  where
    emptyPattern =
      ( EWildP
      , EFuncApp "D.fail" (ELiteral $ EStringL "None of the constructors match"))
    fn1 :: (ConName, ConTag, ContentDecoder) -> ECaseBranch
    fn1 (cname, ctag, cd) =
      let pattern = ELitP (EStringL $ unpack $ ctag)
          expression = contentDecoderToExp mcntFname cname cd
       in (pattern, expression)

decodeUnderConKey :: (ConName, ConTag, ContentDecoder) -> Text -> EExpr
decodeUnderConKey (cname, ctag, cd) _ =
  EFuncApp (EFuncApp "D.field" (ELiteral $ EStringL $ unpack $ ctag)) $
  contentDecoderToExp Nothing cname cd

contentDecoderToExp :: Maybe Text -> ConName -> ContentDecoder -> EExpr
contentDecoderToExp mcntFname cname cd =
  case cd of
    CDRecord nfds ->
      let makerFnName = (prependMk cname)
          makerFn = mkRecorderMaker makerFnName cname nfds
       in ELet [makerFn] $ aggregateDecoders makerFnName $ mapFn <$> nfds
    CDRecordRaw nfd@(_, _, td) ->
      let makerFnName = (prependMk cname)
          makerFn = mkRecorderMaker makerFnName cname [nfd]
       in ELet [makerFn] $ aggregateDecoders makerFnName [getDecoderExpr 0 td]
    CDList tds ->
      let agg = aggregateDecoders cname $ zipWith zipFn [0 ..] tds
       in case mcntFname of
            Just cntFname ->
              EFuncApp
                (EFuncApp "D.field" (ELiteral $ EStringL $ unpack cntFname))
                agg
            Nothing -> agg
    CDRaw td ->
      let agg = aggregateDecoders cname [getDecoderExpr 0 td]
       in case mcntFname of
            Just cntFname ->
              EFuncApp
                (EFuncApp "D.field" (ELiteral $ EStringL $ unpack cntFname))
                agg
            Nothing -> agg
    CDEmpty -> EFuncApp "D.succeed" (EName cname)
  where
    mapFn :: (FieldName, FieldTag, TypeDescriptor) -> EExpr
    mapFn (_, ft, td) =
      case td of
        TDMaybe wtd ->
          EFuncApp
            "D.maybe"
            (EFuncApp
               (EFuncApp "D.field" (ELiteral $ EStringL $ unpack ft))
               (getDecoderExpr 0 wtd))
        _ ->
          EFuncApp
            (EFuncApp "D.field" (ELiteral $ EStringL $ unpack ft))
            (getDecoderExpr 0 td)
    zipFn :: Int -> TypeDescriptor -> EExpr
    zipFn idx td =
      EFuncApp (EFuncApp "D.index" (ELiteral $ EIntL idx)) (getDecoderExpr 0 td)

aggregateDecoders :: Text -> [EExpr] -> EExpr
aggregateDecoders mfn exprs =
  let fieldCount = P.length exprs
      field8 = DL.take 8 exprs
      field8L = P.length field8
      decU8 =
        DL.foldl'
          EFuncApp
          (EFuncApp
             (EName $
              T.concat
                [ "D.map"
                , if field8L > 1
                    then pack $ show field8L
                    else ""
                ])
             (EName mfn)) $
        field8
   in if fieldCount < 9
        then decU8
        else DL.foldl' (\a v -> EFuncApp ((EFuncApp "seqApp") a) v) decU8 $
             DL.drop 8 exprs

mkRecorderMaker ::
     Text -> ConName -> [(FieldName, FieldTag, TypeDescriptor)] -> EDec
mkRecorderMaker rmName cname fds =
  let args = zipWith (\_ y -> T.concat ["a", pack $ show y]) fds [(1 :: Int) ..]
   in EFunc rmName Nothing args $
      EFuncApp (EName cname) (ERec $ zipWith mkField fds args)
  where
    mkField :: (FieldName, FieldTag, TypeDescriptor) -> Text -> EField
    mkField (fn, _, _) a = (fn, EName a)

mkTupleMaker :: Text -> Int -> [TypeDescriptor] -> EDec
mkTupleMaker tmName idx fds =
  let args =
        zipWith
          (\_ y -> T.concat ["a", pack $ show $ idx, "_", pack $ show y])
          fds
          [(1 :: Int) ..]
   in EFunc tmName Nothing args $ ETuple (EName <$> args)

generateEncoder :: (TypeDescriptor, Decoder) -> LibM EDec
generateEncoder (td, decoder) = do
  tdisplay <- mkTypeDisplayFromTd td
  pure $
    case td of
      SimpleType ctdata -> fn ctdata tdisplay
      Polymorphic _ ctdata -> fn ctdata tdisplay
      _ -> error "Encoders/decoders can only be made for user defined types"
  where
    fn :: CTData -> TypeDisplay -> EDec
    fn ctdata tdisp =
      EFunc
        (T.concat ["encode", getCTDataName ctdata])
        (Just $
         T.concat
           [ let TypeDisplay x = tdisp
              in x
           , " -> "
           , "E.Value"
           ])
        ["a"] $
      decoderToEncoderEExpr $ decoder

decoderToEncoderEExpr :: Decoder -> EExpr
decoderToEncoderEExpr d =
  case d of
    DUnderConKey cons_ -> ECase "a" $ mapFn <$> cons_
    DTagged tfn cfn cons_ -> ECase "a" $ mapFn2 tfn cfn <$> cons_
    DTwoElement cons_ -> ECase "a" $ mapFn3 <$> cons_
    DUntagged cons_ -> ECase "a" $ mapFn4 <$> cons_
  where
    mapFn4 :: (ConName, ContentDecoder) -> ECaseBranch
    mapFn4 (cname, cd) =
      (makePattern (cname, "", cd), contentDecoderToEncoderExp Nothing cd)
    mapFn3 :: (ConName, ConTag, ContentDecoder) -> ECaseBranch
    mapFn3 a@(_, ctag, cd) =
      ( makePattern a
      , EFuncApp (EFuncApp "E.list" "identity") $
        EList
          [ EFuncApp "E.string" $ ELiteral $ EStringL $ unpack $ ctag
          , contentDecoderToEncoderExp Nothing cd
          ])
    mapFn2 :: Text -> Text -> (ConName, ConTag, ContentDecoder) -> ECaseBranch
    mapFn2 tfn cfn a = (makePattern a, encoderTagged tfn cfn a)
    mapFn :: (ConName, ConTag, ContentDecoder) -> ECaseBranch
    mapFn a = (makePattern a, encoderUnderConKey a)
    makePattern :: (ConName, ConTag, ContentDecoder) -> EPattern
    makePattern (cname, _, cd) =
      case cd of
        CDRecord _ -> EConsP cname $ [EVarP "x"]
        CDRecordRaw _ -> EConsP cname $ [EVarP "x"]
        CDList tds ->
          EConsP cname $
          zipWith
            (\x _ -> EVarP $ T.concat ["a", pack $ show x])
            [(1 :: Int) ..]
            tds
        CDRaw _ -> EConsP cname [EVarP "a1"]
        CDEmpty -> EConsP cname []

encoderUnderConKey :: (ConName, ConTag, ContentDecoder) -> EExpr
encoderUnderConKey (_, ctag, cd) =
  EFuncApp "E.object" $
  EList
    [ ETuple
        [ ELiteral $ EStringL $ unpack ctag
        , contentDecoderToEncoderExp Nothing cd
        ]
    ]

encoderTagged :: Text -> Text -> (ConName, ConTag, ContentDecoder) -> EExpr
encoderTagged tfn cfn (_, ctag, cd) =
  case cd of
    CDRecord _ -> contentDecoderToEncoderExp (Just (tfn, ctag)) cd
    CDRecordRaw _ -> contentDecoderToEncoderExp Nothing cd
    _ ->
      EFuncApp "E.object" $
      EList $
      [ ETuple
          [ ELiteral $ EStringL $ unpack $ tfn
          , EFuncApp "E.string" $ ELiteral $ EStringL $ unpack $ ctag
          ]
      , ETuple
          [ ELiteral $ EStringL $ unpack $ cfn
          , contentDecoderToEncoderExp Nothing cd
          ]
      ]

contentDecoderToEncoderExp ::
     Maybe (FieldName, ConTag) -> ContentDecoder -> EExpr
contentDecoderToEncoderExp mct cd =
  case cd of
    CDRecord fds ->
      EFuncApp "E.object" $
      case mct of
        Nothing -> EList $ (mapFn <$> fds)
        Just (tn, ctag) ->
          let x =
                (ETuple
                   [ ELiteral $ EStringL $ unpack tn
                   , EFuncApp "E.string" $ ELiteral $ EStringL $ unpack $ ctag
                   ])
           in EList $ x : (mapFn <$> fds)
    CDRecordRaw (fn, _, td) ->
      EFuncApp (getEncoderExpr 0 td) $ EName $ T.concat ["x", ".", fn]
    CDList tds ->
      EFuncApp (EFuncApp "E.list" "identity") $ EList $ zipWith zipFn tds [1 ..]
    CDRaw td -> EFuncApp (getEncoderExpr 0 td) "a1"
    CDEmpty -> EFuncApp (EFuncApp "E.list" "identity") $ EList []
  where
    zipFn :: TypeDescriptor -> Int -> EExpr
    zipFn td idx =
      EFuncApp (getEncoderExpr 0 td) $ EName $ T.concat ["a", pack $ show idx]
    mapFn :: (FieldName, FieldTag, TypeDescriptor) -> EExpr
    mapFn (fn, ft, td) =
      ETuple
        [ ELiteral $ EStringL $ unpack ft
        , EFuncApp (getEncoderExpr 0 td) $ EName $ T.concat ["x", ".", fn]
        ]

getEncoderExpr :: Int -> TypeDescriptor -> EExpr
getEncoderExpr idx (SimpleType ctd) =
  case isTuple $ getCTDName ctd of
    Just _ ->
      let tds =
            case ctd of
              CTData _ ((SimpleConstructor _ netds) :| []) -> NE.toList netds
              CTData _ _ -> []
              CTEmpty _ -> []
       in case tds of
            [] -> ELambda (EFuncApp (EFuncApp "E.list" "identity") $ EList [])
            (_:_) ->
              ELet
                [generateTupleEncoder idx tds]
                (EName $ T.concat ["encodeTuple", pack $ show idx])
    Nothing -> EName $ T.concat ["encode", getCTDName ctd]
getEncoderExpr _ (Polymorphic _ ctd) =
  case isTuple $ getCTDName ctd of
    Just _ -> error "Not implemented"
    Nothing -> EName $ T.concat ["encode", getCTDName ctd]
getEncoderExpr _ (Primitive n _) = EName $ getPrimitiveEncoder n
getEncoderExpr idx (List x) = (EFuncApp "E.list" (getEncoderExpr idx x))
getEncoderExpr idx (TDMaybe x) = (EFuncApp "encodeMaybe" (getEncoderExpr idx x))
getEncoderExpr _ (TRecusrive md) = EName $ T.concat ["encode", _mTypeName md]
getEncoderExpr _ (TExternal (ExInfo _ (Just ei) _) _) =
  EName $ T.concat [extSymbol ei]
getEncoderExpr _ (TExternal (ExInfo _ _ _) _) = error "Encoder not found"
getEncoderExpr _ (TTypeVar _) = error "No encoder for type variable"

getDecoderExpr :: Int -> TypeDescriptor -> EExpr
getDecoderExpr idx td =
  let expr =
        case td of
          SimpleType ctd ->
            case isTuple $ getCTDName ctd of
              Just _ ->
                let tds =
                      case ctd of
                        CTData _ ((SimpleConstructor _ netds) :| []) ->
                          NE.toList netds
                        CTData _ _ -> []
                        CTEmpty _ -> []
                 in case tds of
                      [] -> EFuncApp "D.succeed" "()"
                      (_:_) ->
                        ELet [generateTupleDecoder idx tds] $
                        EName $ T.concat ["decodeTuple", pack $ show $ idx]
              Nothing -> EName $ T.concat ["decode", getCTDName ctd]
          Polymorphic _ ctd ->
            case isTuple $ getCTDName ctd of
              Just c -> EName $ T.concat ["decodeTuple", pack $ show $ c]
              Nothing -> EName $ T.concat ["decode", getCTDName ctd]
          Primitive n _ -> EName $ getPrimitiveDecoder n
          List x -> EFuncApp (EName "D.list") (getDecoderExpr idx x)
          TRecusrive md ->
            EFuncApp "D.lazy" $
            ELambda $ EName $ T.concat ["decode", _mTypeName md]
          TDMaybe x -> (EFuncApp "D.maybe" (getDecoderExpr idx x))
          (TExternal (ExInfo _ _ (Just ei)) _) ->
            EName $ T.concat [extSymbol ei]
          (TExternal (ExInfo _ _ _) _) -> error "Decoder not found"
          (TTypeVar _) -> error "No Decoder for type var"
   in if checkRecursion td
        then EFuncApp "D.lazy" $ ELambda $ expr
        else expr

checkRecursion :: TypeDescriptor -> Bool
checkRecursion td_ =
  case td_ of
    SimpleType ctdata -> any id $ checkRecursion <$> getTypeDescriptors ctdata
    Polymorphic _ ctdata ->
      any id $ checkRecursion <$> getTypeDescriptors ctdata
    List td -> checkRecursion td
    TDMaybe td -> checkRecursion td
    Primitive _ _ -> False
    TRecusrive _ -> True
    TExternal _ _ -> False
    TTypeVar _ -> False
  where
    getTypeDescriptors :: CTData -> [TypeDescriptor]
    getTypeDescriptors (CTEmpty _) = []
    getTypeDescriptors (CTData _ ncd) =
      P.concat $ NE.toList $ NE.map getFromCd ncd
    getFromCd :: ConstructorDescriptor -> [TypeDescriptor]
    getFromCd (RecordConstructor _ fds) =
      NE.toList $ NE.map (\(NamedField _ td) -> td) fds
    getFromCd (SimpleConstructor _ fds) = NE.toList fds
    getFromCd (NullaryConstructor _) = []

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
generateElmDef :: TypeDescriptor -> LibM EDec
generateElmDef td =
  case td of
    SimpleType (CTData tname c) -> do
      defC <- generateElmDefC c
      pure $ EType (tnHead tname) [] defC
    SimpleType (CTEmpty tname) -> do
      pure $ EType (tnHead tname) [] EEmpty
    Polymorphic tvars (CTData tname c) -> do
      defC <- generateElmDefC c
      pure $ EType (tnHead tname) (renderTypeVar <$> tvars) defC
    Polymorphic _targs (CTEmpty tname) ->
      pure $ EType (tnHead tname) undefined EEmpty
    _ -> error "Not implemented"

generateElmDefC :: Constructors -> LibM ECons
generateElmDefC cds = do
  cDefs <- mapM generateElmDefCD $ NE.toList cds
  pure $ ESum cDefs

generateElmDefCD :: ConstructorDescriptor -> LibM ECons
generateElmDefCD cd =
  case cd of
    RecordConstructor cname nfs -> do
      rfs <- generateRecordFields nfs
      pure $ ERecord cname rfs
    SimpleConstructor cname fs -> do
      rfs <- generateUnNamedFields fs
      pure $ EProduct cname rfs
    NullaryConstructor cname -> do
      pure $ ENullary cname

generateRecordFields :: Fields NamedField -> LibM [ENamedField]
generateRecordFields fs =
  case fs of
    (nf :| []) -> mapM mapFn [nf]
    n -> mapM mapFn $ NE.toList n
  where
    mapFn :: NamedField -> LibM ENamedField
    mapFn (NamedField a b) = do
      t <- mkTypeDisplayFromTd b
      pure (a, t)

generateUnNamedFields :: Fields TypeDescriptor -> LibM [TypeDisplay]
generateUnNamedFields fds = mapM mkTypeDisplayFromTd $ NE.toList fds

mkTypeDisplayFromTd :: TypeDescriptor -> LibM TypeDisplay
mkTypeDisplayFromTd td = do
  seen <- ask
  x <-
    case getMDataFromTd td of
      Just md ->
        case hasPoly <$> (DMS.lookup md seen) of
          Just True -> pure $ TypeDisplay $ getRenderedName td
          Just False -> pure $ TypeDisplay $ _mTypeName md
          Nothing -> pure $ TypeDisplay $ getRenderedName td
      Nothing -> pure $ TypeDisplay $ getRenderedName td
  pure x

hasPoly :: [(GenOption, HType)] -> Bool
hasPoly cl = isJust $ DL.find fn cl
  where
    fn :: (GenOption, HType) -> Bool
    fn (Definiton Poly, _) = True
    fn (Everything Poly, _) = True
    fn _ = False

getMDataFromTd :: TypeDescriptor -> Maybe MData
getMDataFromTd td =
  case td of
    SimpleType c -> Just $ getMDataFromCTdata c
    Polymorphic _ c -> Just $ getMDataFromCTdata c
    TRecusrive md -> Just md
    _ -> Nothing

getMDataFromCTdata :: CTData -> MData
getMDataFromCTdata (CTData tn _) = tnMData tn
getMDataFromCTdata (CTEmpty tn) = tnMData tn
