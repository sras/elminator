{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC  -Wno-incomplete-uni-patterns #-}

module Elminator.ELM.Generator
  ( generateElm
  , typeDescriptorToDecoder
  , elmFront
  ) where

import Control.Monad.Reader as R
import Data.Aeson as Aeson
import qualified Data.List as DL
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Maybe
import Data.Text as T hiding (any, zipWith)
import qualified Elminator.ELM.Elm18 as Elm18
import qualified Elminator.ELM.Elm19 as Elm19
import Elminator.ELM.Render
import Elminator.Generics.Simple
import Elminator.Lib
import Language.Haskell.TH
import Prelude
import qualified Prelude as P
import Control.Monad (zipWithM)

elmFront :: Text -> GenM (Text -> Text)
elmFront moduleName = do
  (ev, _) <- ask
  case ev of
    Elm0p19 -> pure $ Elm19.elmFront moduleName
    Elm0p18 -> pure $ Elm18.elmFront moduleName

listEncoder :: GenM EExpr
listEncoder = do
  (ev, _) <- ask
  case ev of
    Elm0p19 -> pure Elm19.listEncoder
    Elm0p18 -> pure Elm18.listEncoder

generateTupleEncoder :: Int -> [TypeDescriptor] -> GenM EDec
generateTupleEncoder idx types = do
  eexpr <- getExpr
  pure $
    EFunc (T.concat ["encodeTuple", pack $ show idx]) Nothing [tlVar] $
    ELet [EBinding (ETupleP patterns) (EName tlVar)] eexpr
  where
    tlVar = T.concat ["a", pack $ show idx, "1"]
    indexVar :: Int -> Text
    indexVar y = T.concat ["b", pack $ show idx, "_", pack $ show y]
    varList :: [Text]
    varList = zipWith (\_ y -> indexVar y) types [1 ..]
    patterns = EVarP <$> varList
    getExpr = do
      le <- listEncoder
      expr <-
        zipWithM
          (\x i -> do
             expr <- getEncoderExpr (idx + 1) x
             pure $ EFuncApp expr (EName $ indexVar i))
          types
          [1 ..]
      pure (EFuncApp (EFuncApp le "identity") $ EList expr)

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

generateElm :: GenOption -> HType -> Options -> GenM Text
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

generateDecoder :: (TypeDescriptor, Decoder) -> GenM EDec
generateDecoder (td, decoder) = do
  tdisplay <- renderType td True True
  case td of
    (TOccupied md _ _ _) -> fn (_mTypeName md) tdisplay
    _ -> error "Encoders/decoders can only be made for user defined types"
  where
    fn :: Text -> Text -> GenM EDec
    fn tn tdisp = do
      x <- decoderToDecoderEExpr decoder
      pure $
        EFunc
          (T.concat ["decode", tn])
          (Just $ T.concat ["D.Decoder ", tdisp])
          []
          x

prependMk :: Text -> Text
prependMk x = T.concat ["mk", x]

decoderToDecoderEExpr :: Decoder -> GenM EExpr
decoderToDecoderEExpr d =
  case d of
    DUnderConKey cds -> do
      exprs <- mapM decodeUnderConKey cds
      pure $ EFuncApp "D.oneOf" (EList exprs)
    DTagged tfn cfn cds -> do
      tryCons <- mkTryCons (Just cfn) cds
      let expr =
            EFuncApp
              (EFuncApp "D.andThen" "tryCons")
              (EFuncApp
                 (EFuncApp "D.field" (ELiteral $ EStringL $ unpack tfn))
                 "D.string")
       in pure $ ELet [tryCons] expr
    DTwoElement cds -> do
      tryCons <- mkTryCons Nothing cds
      let expr =
            EFuncApp
              (EFuncApp
                 "D.andThen"
                 (EInlineApp
                    ">>"
                    "tryCons"
                    (EFuncApp "D.index" (ELiteral $ EIntL 1))))
              (EFuncApp (EFuncApp "D.index" (ELiteral $ EIntL 0)) "D.string")
       in pure $ ELet [tryCons] expr
    DUntagged cds -> do
      exprs <- mapM (uncurry (contentDecoderToExp Nothing)) cds
      pure $ EFuncApp "D.oneOf" (EList exprs)

mkTryCons :: Maybe Text -> [(ConName, ConTag, ContentDecoder)] -> GenM EDec
mkTryCons mcntFname cds = do
  cbs <- mapM fn1 cds
  pure $ EFunc "tryCons" Nothing ["v"] $ ECase "v" (cbs ++ [emptyPattern])
  where
    emptyPattern =
      ( EWildP
      , EFuncApp "D.fail" (ELiteral $ EStringL "None of the constructors match"))
    fn1 :: (ConName, ConTag, ContentDecoder) -> GenM ECaseBranch
    fn1 (cname, ctag, cd) = do
      expression <- contentDecoderToExp mcntFname cname cd
      let pat = ELitP (EStringL $ unpack ctag)
       in pure (pat, expression)

decodeUnderConKey :: (ConName, ConTag, ContentDecoder) -> GenM EExpr
decodeUnderConKey (cname, ctag, cd) = do
  decoderExp <- contentDecoderToExp Nothing cname cd
  pure $
    EFuncApp (EFuncApp "D.field" (ELiteral $ EStringL $ unpack ctag)) decoderExp

contentDecoderToExp :: Maybe Text -> ConName -> ContentDecoder -> GenM EExpr
contentDecoderToExp mcntFname cname cd =
  pure $
  case cd of
    CDRecord nfds ->
      let makerFnName = prependMk cname
          makerFn = mkRecorderMaker makerFnName cname nfds
       in ELet [makerFn] $ aggregateDecoders makerFnName $ mapFn <$> nfds
    CDRecordRaw nfd@(_, _, td) ->
      let makerFnName = prependMk cname
          makerFn = mkRecorderMaker makerFnName cname [nfd]
          agg = aggregateDecoders makerFnName [getDecoderExpr 0 td]
       in ELet [makerFn] $
          case mcntFname of
            Just cntFname ->
              EFuncApp
                (EFuncApp "D.field" (ELiteral $ EStringL $ unpack cntFname))
                agg
            _ -> agg
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

generateEncoder :: (TypeDescriptor, Decoder) -> GenM EDec
generateEncoder (td, decoder) = do
  tdisplay <- renderType td False True
  case td of
    (TOccupied md _ _ _) -> fn (_mTypeName md) tdisplay
    _ -> error "Encoders/decoders can only be made for user defined types"
  where
    fn :: Text -> Text -> GenM EDec
    fn tname tdisp = do
      expr <- decoderToEncoderEExpr decoder
      pure $
        EFunc
          (T.concat ["encode", tname])
          (Just $ T.concat [tdisp, " -> ", "E.Value"])
          ["a"]
          expr

decoderToEncoderEExpr :: Decoder -> GenM EExpr
decoderToEncoderEExpr d =
  case d of
    DUnderConKey cons_ -> do
      cb <- mapM mapFn cons_
      pure $ ECase "a" cb
    DTagged tfn cfn cons_ -> do
      expr <- mapM (mapFn2 tfn cfn) cons_
      pure $ ECase "a" expr
    DTwoElement cons_ -> do
      expr <- mapM mapFn3 cons_
      pure $ ECase "a" expr
    DUntagged cons_ -> do
      bs <- mapM mapFn4 cons_
      pure $ ECase "a" bs
  where
    mapFn4 :: (ConName, ContentDecoder) -> GenM ECaseBranch
    mapFn4 (cname, cd) = do
      expr <- contentDecoderToEncoderExp Nothing cd
      pure (makePattern (cname, "", cd), expr)
    mapFn3 :: (ConName, ConTag, ContentDecoder) -> GenM ECaseBranch
    mapFn3 a@(_, ctag, cd) = do
      exprs <- contentDecoderToEncoderExp Nothing cd
      le <- listEncoder
      pure
        ( makePattern a
        , EFuncApp (EFuncApp le "identity") $
          EList [EFuncApp "E.string" $ ELiteral $ EStringL $ unpack ctag, exprs])
    mapFn2 ::
         Text -> Text -> (ConName, ConTag, ContentDecoder) -> GenM ECaseBranch
    mapFn2 tfn cfn a = do
      expr <- encoderTagged tfn cfn a
      pure (makePattern a, expr)
    mapFn :: (ConName, ConTag, ContentDecoder) -> GenM ECaseBranch
    mapFn a = do
      expr <- encoderUnderConKey a
      pure (makePattern a, expr)
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

encoderUnderConKey :: (ConName, ConTag, ContentDecoder) -> GenM EExpr
encoderUnderConKey (_, ctag, cd) = do
  decoderExp <- contentDecoderToEncoderExp Nothing cd
  pure $
    EFuncApp "E.object" $
    EList [ETuple [ELiteral $ EStringL $ unpack ctag, decoderExp]]

encoderTagged :: Text -> Text -> (ConName, ConTag, ContentDecoder) -> GenM EExpr
encoderTagged tfn cfn (_, ctag, cd) =
  case cd of
    CDRecord _ -> contentDecoderToEncoderExp (Just (tfn, ctag)) cd
    CDRecordRaw _ -> contentDecoderToEncoderExp Nothing cd
    _ -> do
      encExp <- contentDecoderToEncoderExp Nothing cd
      pure $
        EFuncApp "E.object" $
        EList
          [ ETuple
              [ ELiteral $ EStringL $ unpack tfn
              , EFuncApp "E.string" $ ELiteral $ EStringL $ unpack ctag
              ]
          , ETuple [ELiteral $ EStringL $ unpack cfn, encExp]
          ]

contentDecoderToEncoderExp ::
     Maybe (FieldName, ConTag) -> ContentDecoder -> GenM EExpr
contentDecoderToEncoderExp mct cd =
  case cd of
    CDRecord fds -> do
      es <- mapM mapFn fds
      pure $
        EFuncApp "E.object" $
        case mct of
          Nothing -> EList es
          Just (tn, ctag) ->
            let x =
                  ETuple
                    [ ELiteral $ EStringL $ unpack tn
                    , EFuncApp "E.string" $ ELiteral $ EStringL $ unpack ctag
                    ]
             in EList $ x : es
    CDRecordRaw (fn, _, td) -> do
      encoderExp <- getEncoderExpr 0 td
      pure $ EFuncApp encoderExp $ EName $ T.concat ["x", ".", fn]
    CDList tds -> do
      ls <- zipWithM zipFn tds [1 ..]
      le <- listEncoder
      pure $ EFuncApp (EFuncApp le "identity") $ EList ls
    CDRaw td -> do
      eexp <- getEncoderExpr 0 td
      pure $ EFuncApp eexp "a1"
    CDEmpty -> do
      le <- listEncoder
      pure $ EFuncApp (EFuncApp le "identity") $ EList []
  where
    zipFn :: TypeDescriptor -> Int -> GenM EExpr
    zipFn td idx = do
      encodeExp <- getEncoderExpr 0 td
      pure $ EFuncApp encodeExp $ EName $ T.concat ["a", pack $ show idx]
    mapFn :: (FieldName, FieldTag, TypeDescriptor) -> GenM EExpr
    mapFn (fn, ft, td) = do
      encoderName <- getEncoderExpr 0 td
      pure $
        ETuple
          [ ELiteral $ EStringL $ unpack ft
          , EFuncApp encoderName $ EName $ T.concat ["x", ".", fn]
          ]

getEncoderExpr :: Int -> TypeDescriptor -> GenM EExpr
getEncoderExpr idx (TTuple tds) = do
  expr <- generateTupleEncoder idx tds
  le <- listEncoder
  case tds of
    [] -> pure $ ELambda (EFuncApp (EFuncApp le "identity") $ EList [])
    (_:_) ->
      pure $ ELet [expr] (EName $ T.concat ["encodeTuple", pack $ show idx])
getEncoderExpr _ (TOccupied md _ _ _) =
  pure $ EName $ T.concat ["encode", _mTypeName md]
getEncoderExpr _ (TPrimitive n) =
  pure $ EName $ getPrimitiveEncoder $ _mTypeName n
getEncoderExpr idx (TList x) = do
  le <- listEncoder
  eexp <- getEncoderExpr idx x
  pure $ EFuncApp le eexp
getEncoderExpr idx (TMaybe x) = do
  expr <- getEncoderExpr idx x
  pure $ EFuncApp "encodeMaybe" expr
getEncoderExpr _ (TRecusrive md) =
  pure $ EName $ T.concat ["encode", _mTypeName md]
getEncoderExpr _ (TExternal (ExInfo _ (Just ei) _ _)) =
  pure $ EName $ T.concat [snd ei]
getEncoderExpr _ (TExternal ExInfo {}) = error "Encoder not found"
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
          TMaybe x -> (EFuncApp "D.nullable" (getDecoderExpr idx x))
          TExternal (ExInfo _ _ (Just ei) _) -> EName $ T.concat [snd ei]
          TExternal ExInfo {} -> error "Decoder not found"
          TVar _ -> error "Decoder not found"
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
    TVar _ -> False
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
getPrimitiveDecoder s = T.concat ["decode", s]

getPrimitiveEncoder :: Text -> Text
getPrimitiveEncoder "String" = "E.string"
getPrimitiveEncoder "Int" = "E.int"
getPrimitiveEncoder "Float" = "E.float"
getPrimitiveEncoder "Bool" = "E.bool"
getPrimitiveEncoder s = T.concat ["encode", s]

-- | Generate Elm type definitions
generateElmDef :: TypeDescriptor -> Bool -> GenM EDec
generateElmDef td needPoly =
  case td of
    TEmpty (MData a _ _) tvars _ ->
      pure $ EType a (getTypeVars tvars needPoly) EEmpty
    TOccupied (MData a _ _) (ReifyInfo tvars cnstrs) _ c -> do
      defC <-
        if needPoly
          then case NE.nonEmpty cnstrs of
                 Just nec -> generateElmDefC $ NE.zipWith injectTypeVars nec c
                 Nothing -> error "No constructors obtained from reify"
          else generateElmDefC c
      pure $ EType a (getTypeVars tvars needPoly) defC
    _ -> error "Can only create definitions for use defined types"

getTypeVars :: [TypeVar] -> Bool -> [Text]
getTypeVars tds needPoly =
  if needPoly
    then renderTypeVar <$> tds
    else []

injectTypeVars :: Con -> ConstructorDescriptor -> ConstructorDescriptor
injectTypeVars (RecC _ vbt) (RecordConstructor name flds) =
  case NE.nonEmpty $ (\(_, _, t) -> t) <$> vbt of
    Just tps -> RecordConstructor name (NE.zipWith zipFn tps flds)
    Nothing -> error "Non empty fields expected"
  where
    zipFn :: Type -> (Text, TypeDescriptor) -> (Text, TypeDescriptor)
    zipFn typ (n, td) = (n, injectTypeVarIntoTD typ td)
injectTypeVars (NormalC _ bt) (SimpleConstructor name flds) =
  case NE.nonEmpty $ snd <$> bt of
    Just tps -> SimpleConstructor name (NE.zipWith injectTypeVarIntoTD tps flds)
    Nothing -> error "Non empty fields expected"
injectTypeVars _ n@(NullaryConstructor _) = n
injectTypeVars _ _ = error "Constructor mismatch"

injectTypeVarIntoTD :: Type -> TypeDescriptor -> TypeDescriptor
injectTypeVarIntoTD (VarT n) _ = TVar n
injectTypeVarIntoTD (AppT t1 t2) td =
  case td of
    TEmpty md tvr tds ->
      let tailTd = injectTypeVarIntoTD t2 (Prelude.last tds)
          TEmpty _ _ newtds =
            injectTypeVarIntoTD t1 (TEmpty md tvr (Prelude.init tds))
       in TEmpty md tvr $ newtds ++ [tailTd]
    TOccupied md ri tds cnstrs ->
      let tailTd = injectTypeVarIntoTD t2 (Prelude.last tds)
          TOccupied _ _ newtds _ =
            injectTypeVarIntoTD t1 (TOccupied md ri (Prelude.init tds) cnstrs)
       in TOccupied md ri (newtds ++ [tailTd]) cnstrs
    TTuple tds ->
      let TTuple newtds = injectTypeVarIntoTD t1 (TTuple $ Prelude.init tds)
          tailTd = injectTypeVarIntoTD t2 (Prelude.last tds)
       in TTuple (newtds ++ [tailTd])
    TExternal ei ->
      let tds = exTypeArgs ei
          tailTd = injectTypeVarIntoTD t2 (Prelude.last tds)
          TExternal ExInfo {exTypeArgs = newTds} =
            injectTypeVarIntoTD
              t1
              (TExternal $ ei {exTypeArgs = Prelude.init tds})
       in TExternal $ ei {exTypeArgs = newTds ++ [tailTd]}
    TMaybe tdc -> TMaybe $ injectTypeVarIntoTD t2 tdc
    TList tdc -> TList $ injectTypeVarIntoTD t2 tdc
    td_ -> td_
injectTypeVarIntoTD _ td = td

generateElmDefC :: Constructors -> GenM ECons
generateElmDefC cds = do
  cDefs <- mapM generateElmDefCD $ NE.toList cds
  pure $ ESum cDefs

generateElmDefCD :: ConstructorDescriptor -> GenM ECons
generateElmDefCD cd =
  case cd of
    RecordConstructor cname nfs -> do
      rfs <- generateRecordFields nfs
      pure $ ERecord cname rfs
    SimpleConstructor cname fs -> do
      rfs <- generateUnNamedFields fs
      pure $ EProduct cname rfs
    NullaryConstructor cname -> pure $ ENullary cname

generateRecordFields :: NE.NonEmpty (Text, TypeDescriptor) -> GenM [ENamedField]
generateRecordFields fs =
  case fs of
    (nf :| []) -> mapM mapFn [nf]
    n -> mapM mapFn $ NE.toList n
  where
    mapFn :: (Text, TypeDescriptor) -> GenM ENamedField
    mapFn (a, b) = do
      x <- renderType b False False
      pure (a, x)

generateUnNamedFields :: NE.NonEmpty TypeDescriptor -> GenM [Text]
generateUnNamedFields fds = mapM (\x -> renderType x True False) $ NE.toList fds
