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
import Data.Maybe
import Data.Text as T hiding (any, zipWith)
import Elminator.ELM.CodeGen
import Elminator.Generics.Simple
import Elminator.Lib
import Language.Haskell.TH
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
  \  Nothing -> E.null"
    ]

generateTupleEncoder :: Int -> [TypeDescriptor] -> EDec
generateTupleEncoder idx types =
  EFunc (T.concat ["encodeTuple", pack $ show idx]) Nothing [tlVar] $
  ELet [EBinding (ETupleP patterns) (EName tlVar)] eexpr
  where
    tlVar = T.concat ["a", pack $ show idx, "1"]
    indexVar :: Int -> Text
    indexVar y = T.concat ["b", pack $ show idx, "_", pack $ show y]
    varList :: [Text]
    varList = zipWith (\_ y -> indexVar y) types [1 ..]
    patterns = EVarP <$> varList
    eexpr =
      EFuncApp (EFuncApp "E.list" "identity") $
      EList $
      zipWith
        (\x i -> EFuncApp (getEncoderExpr (idx + 1) x) (EName $ indexVar i))
        types
        [1 ..]

generateTupleDecoder :: Int -> [TypeDescriptor] -> EDec
generateTupleDecoder nidx types =
  EFunc (T.concat ["decodeTuple", pack $ show nidx]) Nothing [] $
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
  td <- toTypeDescriptor h
  collectExtRefs td
  src <-
    case d of
      Definiton Mono -> do
        def <- generateElmDef td False
        pure $ ElmSrc [def]
      Definiton Poly -> do
        def <- generateElmDef td True
        pure $ ElmSrc [def]
      Everything Mono -> do
        let decoder = typeDescriptorToDecoder opts td
        def <- generateElmDef td False
        encSrc <- generateEncoder (td, decoder)
        decSrc <- generateDecoder (td, decoder)
        pure $ ElmSrc [def, encSrc, decSrc]
      Everything Poly -> do
        def <- generateElmDef td True
        let decoder = typeDescriptorToDecoder opts td
        encSrc <- generateEncoder (td, decoder)
        decSrc <- generateDecoder (td, decoder)
        pure $ ElmSrc [def, encSrc, decSrc]
      EncoderDecoder -> do
        let decoder = typeDescriptorToDecoder opts td
        encSrc <- generateEncoder (td, decoder)
        decSrc <- generateDecoder (td, decoder)
        pure $ ElmSrc [encSrc, decSrc]
  pure $ renderElm src

generateDecoder :: (TypeDescriptor, Decoder) -> LibM EDec
generateDecoder (td, decoder) = do
  tdisplay <- renderType td
  pure $
    case td of
      (TOccupied md _ _ _) -> fn (_mTypeName md) tdisplay
      _ -> error "Encoders/decoders can only be made for user defined types"
  where
    fn :: Text -> Text -> EDec
    fn tn tdisp =
      EFunc
        (T.concat ["decode", tn])
        (Just $ T.concat ["D.Decoder", " (", tdisp, ")"])
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
        (EList $ zipWith decodeUnderConKey cds (prependMk . firstOf3 <$> cds))
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
      EFuncApp "D.oneOf" (EList $ uncurry (contentDecoderToExp Nothing) <$> cds)

mkTryCons :: Maybe Text -> [(ConName, ConTag, ContentDecoder)] -> EDec
mkTryCons mcntFname cds =
  EFunc "tryCons" Nothing ["v"] $ ECase "v" ((fn1 <$> cds) ++ [emptyPattern])
  where
    emptyPattern =
      ( EWildP
      , EFuncApp "D.fail" (ELiteral $ EStringL "None of the constructors match"))
    fn1 :: (ConName, ConTag, ContentDecoder) -> ECaseBranch
    fn1 (cname, ctag, cd) =
      let pat = ELitP (EStringL $ unpack ctag)
          expression = contentDecoderToExp mcntFname cname cd
       in (pat, expression)

decodeUnderConKey :: (ConName, ConTag, ContentDecoder) -> Text -> EExpr
decodeUnderConKey (cname, ctag, cd) _ =
  EFuncApp (EFuncApp "D.field" (ELiteral $ EStringL $ unpack ctag)) $
  contentDecoderToExp Nothing cname cd

contentDecoderToExp :: Maybe Text -> ConName -> ContentDecoder -> EExpr
contentDecoderToExp mcntFname cname cd =
  case cd of
    CDRecord nfds ->
      let makerFnName = prependMk cname
          makerFn = mkRecorderMaker makerFnName cname nfds
       in ELet [makerFn] $ aggregateDecoders makerFnName $ mapFn <$> nfds
    CDRecordRaw nfd@(_, _, td) ->
      let makerFnName = prependMk cname
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
        TMaybe wtd ->
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
             (EName mfn))
          field8
   in if fieldCount < 9
        then decU8
        else DL.foldl' (\a v -> EFuncApp (EFuncApp "seqApp" a) v) decU8 $
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
          (\_ y -> T.concat ["a", pack $ show idx, "_", pack $ show y])
          fds
          [(1 :: Int) ..]
   in EFunc tmName Nothing args $ ETuple (EName <$> args)

generateEncoder :: (TypeDescriptor, Decoder) -> LibM EDec
generateEncoder (td, decoder) = do
  tdisplay <- renderType td
  pure $
    case td of
      (TOccupied md _ _ _) -> fn (_mTypeName md) tdisplay
      _ -> error "Encoders/decoders can only be made for user defined types"
  where
    fn :: Text -> Text -> EDec
    fn tname tdisp =
      EFunc
        (T.concat ["encode", tname])
        (Just $ T.concat [tdisp, " -> ", "E.Value"])
        ["a"] $
      decoderToEncoderEExpr decoder

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
          [ EFuncApp "E.string" $ ELiteral $ EStringL $ unpack ctag
          , contentDecoderToEncoderExp Nothing cd
          ])
    mapFn2 :: Text -> Text -> (ConName, ConTag, ContentDecoder) -> ECaseBranch
    mapFn2 tfn cfn a = (makePattern a, encoderTagged tfn cfn a)
    mapFn :: (ConName, ConTag, ContentDecoder) -> ECaseBranch
    mapFn a = (makePattern a, encoderUnderConKey a)
    makePattern :: (ConName, ConTag, ContentDecoder) -> EPattern
    makePattern (cname, _, cd) =
      case cd of
        CDRecord _ -> EConsP cname [EVarP "x"]
        CDRecordRaw _ -> EConsP cname [EVarP "x"]
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
      EList
        [ ETuple
            [ ELiteral $ EStringL $ unpack tfn
            , EFuncApp "E.string" $ ELiteral $ EStringL $ unpack ctag
            ]
        , ETuple
            [ ELiteral $ EStringL $ unpack cfn
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
        Nothing -> EList (mapFn <$> fds)
        Just (tn, ctag) ->
          let x =
                ETuple
                  [ ELiteral $ EStringL $ unpack tn
                  , EFuncApp "E.string" $ ELiteral $ EStringL $ unpack ctag
                  ]
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
getEncoderExpr idx (TTuple tds) =
  case tds of
    [] -> ELambda (EFuncApp (EFuncApp "E.list" "identity") $ EList [])
    (_:_) ->
      ELet
        [generateTupleEncoder idx tds]
        (EName $ T.concat ["encodeTuple", pack $ show idx])
getEncoderExpr _ (TOccupied md _ _ _) =
  EName $ T.concat ["encode", _mTypeName md]
getEncoderExpr _ (TPrimitive n) = EName $ getPrimitiveEncoder $ _mTypeName n
getEncoderExpr idx (TList x) = EFuncApp "E.list" (getEncoderExpr idx x)
getEncoderExpr idx (TMaybe x) = EFuncApp "encodeMaybe" (getEncoderExpr idx x)
getEncoderExpr _ (TRecusrive md) = EName $ T.concat ["encode", _mTypeName md]
getEncoderExpr _ (TExternal (ExInfo _ (Just ei) _ _)) =
  EName $ T.concat [snd ei]
getEncoderExpr _ (TExternal (ExInfo {})) = error "Encoder not found"
getEncoderExpr _ _ = error "Encoder not found"

getDecoderExpr :: Int -> TypeDescriptor -> EExpr
getDecoderExpr idx td =
  let expr =
        case td of
          TEmpty {} -> error "Cannot decode empty types"
          TTuple tds ->
            case tds of
              [] -> EFuncApp "D.succeed" "()"
              (_:_) ->
                ELet [generateTupleDecoder idx tds] $
                EName $ T.concat ["decodeTuple", pack $ show idx]
          TOccupied md _ _ _ -> EName $ T.concat ["decode", _mTypeName md]
          TPrimitive n -> EName $ getPrimitiveDecoder $ _mTypeName n
          TList x -> EFuncApp (EName "D.list") (getDecoderExpr idx x)
          TRecusrive md ->
            EFuncApp "D.lazy" $
            ELambda $ EName $ T.concat ["decode", _mTypeName md]
          TMaybe x -> (EFuncApp "D.maybe" (getDecoderExpr idx x))
          TExternal (ExInfo _ _ (Just ei) _) -> EName $ T.concat [snd ei]
          TExternal ExInfo {} -> error "Decoder not found"
   in if checkRecursion td
        then EFuncApp "D.lazy" $ ELambda expr
        else expr

checkRecursion :: TypeDescriptor -> Bool
checkRecursion td_ =
  case td_ of
    TOccupied _ _ _ cnstrs -> or $ checkRecursion <$> getTypeDescriptors cnstrs
    TList td -> checkRecursion td
    TMaybe td -> checkRecursion td
    TPrimitive _ -> False
    TRecusrive _ -> True
    TExternal _ -> False
    TTuple tds -> or $ checkRecursion <$> tds
    TEmpty {} -> False
  where
    getTypeDescriptors :: Constructors -> [TypeDescriptor]
    getTypeDescriptors ncd = P.concat $ NE.toList $ NE.map getFromCd ncd
    getFromCd :: ConstructorDescriptor -> [TypeDescriptor]
    getFromCd (RecordConstructor _ fds) = NE.toList $ NE.map snd fds
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
generateElmDef :: TypeDescriptor -> Bool -> LibM EDec
generateElmDef td needPoly =
  case td of
    TEmpty (MData a _ _) tvars _ ->
      pure $ EType a (getTypeVars tvars needPoly) EEmpty
    TOccupied (MData a _ _) (ReifyInfo tvars cnstrs) _ c -> do
      defC <-
        if needPoly
          then generateElmDecTHCS cnstrs
          else generateElmDefC c
      pure $ EType a (getTypeVars tvars needPoly) defC
    _ -> error "Can only create definitions for use defined types"

getTypeVars :: [TypeVar] -> Bool -> [Text]
getTypeVars tds needPoly =
  if needPoly
    then renderTypeVar <$> tds
    else []

generateElmDecTHCS :: [Con] -> LibM ECons
generateElmDecTHCS cs = do
  a <- mapM generateElmDecTHC cs
  pure $ ESum a

generateElmDecTHC :: Con -> LibM ECons
generateElmDecTHC (NormalC n tx) = do
  ds <- mapM (\(_, t) -> wrapInPara <$> renderTHType t) tx
  pure $ EProduct (pack $ nameToText n) ds
generateElmDecTHC (RecC n tx) = do
  ds <-
    mapM
      (\(nm, _, t) -> do
         x <- renderTHType t
         pure (pack $ nameToText nm, x))
      tx
  pure $ ERecord (pack $ nameToText n) ds
generateElmDecTHC _ = error "Not implemented"

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
    NullaryConstructor cname -> pure $ ENullary cname

generateRecordFields :: NE.NonEmpty (Text, TypeDescriptor) -> LibM [ENamedField]
generateRecordFields fs =
  case fs of
    (nf :| []) -> mapM mapFn [nf]
    n -> mapM mapFn $ NE.toList n
  where
    mapFn :: (Text, TypeDescriptor) -> LibM ENamedField
    mapFn (a, b) = do
      x <- renderType b
      pure (a, x)

generateUnNamedFields :: NE.NonEmpty TypeDescriptor -> LibM [Text]
generateUnNamedFields fds = mapM renderType $ NE.toList fds
