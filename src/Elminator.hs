{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}

module Elminator (generateElmDef, ToHType) where

import Generics.Simple
import Data.Text as T
import NeatInterpolation
import Data.Proxy
import Language.Haskell.TH
import qualified Data.List as DL

generateElmDef :: (ToHType a) => Proxy a -> Q Exp
generateElmDef p = do
  let hType = toHType p
  runIO $ putStrLn $ show $ hType
  def <- generateElmDef' $ hType
  pure $ LitE $ StringL def
  where
  generateElmDef' :: HType -> Q String
  generateElmDef' (HTypePrimitive p) = pure ""
  generateElmDef' (HTypeProduct (HConstructor cname) fields@((HField (Just _) _):_)) = do
    fieldsSrc <- generateRecordFields fields
    pure $ T.unpack $ [text|type alias $cname = $cname $fieldsSrc |]
  generateElmDef' (HTypeProduct (HConstructor cname) fields@((HField Nothing _):_)) = do
    fieldsSrc <- generateProductFields fields
    pure $ T.unpack $ [text|type $cname = $cname $fieldsSrc |]
  generateElmDef' (HTypeWithMeta _ x) = generateElmDef' x

generateRecordFields :: [HField] -> Q Text
generateRecordFields fields = do
  pairs <- mapM mapFn fields
  pure $ let src = intercalate "," pairs in [text| { $src } |]
  where
    mapFn :: HField -> Q Text
    mapFn (HField (Just fname) typ) = do
      tname <- getTypeName typ
      pure [text|$fname = $tname|]

generateProductFields :: [HField] -> Q Text
generateProductFields fields = do
  pairs <- mapM mapFn fields
  let src = intercalate " " pairs
  pure [text| $src|]
  where
    mapFn :: HField -> Q Text
    mapFn (HField Nothing typ) = getTypeName typ

getTypeName :: HType -> Q Text
getTypeName (HTypeWithMeta (MData x _ _) _) = do
  mtName <- lookupTypeName $ unpack x
  case mtName of
    Just tName -> do
      info <- reify tName
      runIO $ putStrLn $ show $ getTypeConstructorArgs info
      pure x
    Nothing -> error $ unpack $ [text|Cannot find type with name $x in scope|]
getTypeName (HTypePrimitive x) = getPrimitiveName x
getTypeName _ = error "Type name not available"

getPrimitiveName :: HPrimitive -> Q Text
getPrimitiveName HInt = pure "Int"
getPrimitiveName HString = pure "String"

data TVCL = TVCL Con Int deriving (Show) -- Location of the type variables location in the constructor

getTypeConstructorArgs :: Info -> [TVCL]
getTypeConstructorArgs (TyConI d) = getTVCL d
  where
    getTVCL :: Dec -> [TVCL]
    getTVCL (DataD _ name args _ constructors _) = (locateTa constructors . getName) <$> args
      where
      getName :: TyVarBndr -> Name
      getName (PlainTV x) = x
      getName (KindedTV x _) = x
      locateTa :: [Con] -> Name -> TVCL
      locateTa [] n = error "Failed to locate type variable in construct"
      locateTa (c:cs) n =
        case lookupTaInConstructor c n of
          Just x -> TVCL c x
          Nothing -> locateTa cs n
        where
        lookupTaInConstructor :: Con -> Name -> Maybe Int
        lookupTaInConstructor c n = DL.elemIndex (Just n) (getConstructorArgs c)
          where
          getConstructorArgs :: Con -> [Maybe Name]
          getConstructorArgs (NormalC _ args) = (getTvName . snd) <$> args
          getConstructorArgs (RecC _ args) = (\(_, _, a) -> getTvName a) <$> args
          getConstructorArgs _ = error "Unsupported Constructor Type"
          getTvName :: Type -> Maybe Name
          getTvName (VarT n) = Just n
