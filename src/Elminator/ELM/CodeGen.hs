{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module Elminator.ELM.CodeGen where

import Control.Monad.State.Lazy
import qualified Data.List as DL
import Data.String
import Data.Text as T hiding (foldr)

type CurrentPos = Int

type CurrentIndent = Int

type RenderM = State (CurrentIndent, CurrentPos, Text)

renderElm :: ElmSrc -> Text
renderElm (ElmSrc decs) =
  let (_, _, srcs) =
        execState
          (mapM_
             (\x -> do
                renderElmDec x
                renderNL
                renderNL
                resetIndent)
             decs)
          (0, 0, "")
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
  sequence_ $
    (\x -> do
       s
       fn x) <$>
    tx

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
setCI i = modify (\(_, p, t) -> (i, p, t))

resetIndent :: RenderM ()
resetIndent = setCI 0

incIndent :: RenderM ()
incIndent = do
  modify (\(i, p, t) -> (i + 1, p, t))

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
  if DL.length targs > 0
    then renderSpace
    else pure ()
  renderIC (renderSpace) targs renderText
  renderSpace
  renderText "="
  renderSpace
  renderCon cons_
  resetIndent
renderElmDec (EFunc name sig fargs expr) = do
  case sig of
    Just s -> renderText $ T.concat [name, " : ", s]
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
renderElmDec (EBinding patt expr) = do
  renderNL
  renderCI
  renderPattern patt
  renderText " = "
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
  renderIC
    (do renderNL
        renderCI)
    decs
    renderElmDec
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
  renderIC
    (do renderNL
        renderCI)
    branches
    renderCaseBranch
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
  renderIC
    (do renderNL
        setCI p
        renderCI
        renderText ", ")
    l
    renderExp
  renderText "]"
  setCI i
renderExp (ELiteral l) = renderLiteral l
renderExp (ETuple l) = do
  renderText "("
  renderIC (renderText ", ") l renderExp
  renderText ")"
renderExp (ELambda expr) = do
  renderText "(\\_ -> "
  renderExp expr
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
renderPattern (ETupleP ps) = do
  renderText "("
  renderIC (renderText ",") ps renderPattern
  renderText ")"
renderPattern (EListP ps) = do
  renderText "["
  renderIC (renderText ",") ps renderPattern
  renderText "]"
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
  renderIC (renderText ", ") fds (renderText . renderNamedField)
  renderText " } "
renderCon (EProduct cname fds) = do
  renderText cname
  renderSpace
  renderIC (renderText " ") (fds) (renderText . renderType)
renderCon (ESum cons_) = renderIC (renderText " | ") cons_ renderCon
renderCon (ENullary con) = renderText con
renderCon EEmpty = renderText ""

renderType :: TypeDisplay -> Text
renderType (TypeDisplay x) = x

renderNamedField :: ENamedField -> Text
renderNamedField (name, td) = T.concat [name, " : ", renderType td]

-- | Elm code gen
type TArg = Text

type FArg = Text

type FSig = Maybe Text

data ElmSrc =
  ElmSrc [EDec]

data EDec
  = EFunc Text FSig [FArg] EExpr
  | EType Text [TArg] ECons
  | EBinding EPattern EExpr
  deriving (Show, Eq)

data ECons
  = ERecord Text [ENamedField]
  | EProduct Text [TypeDisplay]
  | ESum [ECons]
  | ENullary Text
  | EEmpty
  deriving (Show, Eq)

data TypeDisplay =
  TypeDisplay Text
  deriving (Show, Eq)

type ENamedField = (Text, TypeDisplay)

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
  | ELambda EExpr
  deriving (Eq, Show)

instance IsString EExpr where
  fromString = (EName) . pack

type EField = (Text, EExpr)

type EBinding = (EPattern, EExpr)

data ELit
  = EStringL String
  | EIntL Int
  deriving (Eq, Show)

type ECaseBranch = (EPattern, EExpr)

data EPattern
  = EVarP Text
  | EConsP Text [EPattern]
  | ELitP ELit
  | ETupleP [EPattern]
  | EListP [EPattern]
  | EWildP
  deriving (Eq, Show)
