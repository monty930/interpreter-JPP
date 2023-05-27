module Helper where

import AbsGrammar
import Types 
import qualified Data.Map as M

getIdentString :: Ident -> String
getIdentString (Ident str) = str

getArgIdent :: Arg -> Ident
getArgIdent (Arg_T _ _ ident) = ident
getArgIdent _ = undefined -- intended

stringTypeOfArg :: Arg -> String
stringTypeOfArg (Arg_T _ type_ _) = case type_ of
  Int_T _ -> "int"
  CharT_T _ -> "char"
  Str_T _ -> "string"
  Bool_T _ -> "bool"
stringTypeOfArg _ = undefined -- intended

stringTypeOfElit :: ELit -> String
stringTypeOfElit (ELitInt_T _ _) = "int"
stringTypeOfElit (EChar_T _ _) = "char"
stringTypeOfElit (EString_T _ _) = "string"
stringTypeOfElit (ELitBool_T _ _) = "bool"

stringTypeOfType :: Type -> String
stringTypeOfType type_ = case type_ of
  Int_T _ -> "int"
  CharT_T _ -> "char"
  Str_T _ -> "string"
  Bool_T _ -> "bool"

stringFunctionType :: RetVal -> String
stringFunctionType (FunRetVal_T _ type_) = stringTypeOfType type_
stringFunctionType (FunRetVoid_T _) = "void"

typeOfArg :: Arg -> Type
typeOfArg (Arg_T _ type_ _) = type_
typeOfArg _ = undefined -- intended

showBNFC :: BNFC'Position -> String
showBNFC (Just (line, col)) = "line " ++ show line ++ ", column " ++ show col
showBNFC Nothing = ""

makeError message bnfcPos = do
  let errorMessage = showBNFC bnfcPos ++ " " ++ message
  errorWithoutStackTrace errorMessage

makeTypeError message bnfcPos = do
  let errorMessage = "[type checker] " ++ showBNFC bnfcPos ++ " " ++ message
  errorWithoutStackTrace errorMessage

getNewLoc :: StoreVar -> Loc
getNewLoc stVar =
  case M.keys stVar of
    [] -> 0
    keys -> maximum keys + 1

getNewLocForGen :: StoreIter -> Loc
getNewLocForGen stIter =
  case M.keys stIter of
    [] -> 0
    keys -> maximum keys + 1

getNewLocForList :: StoreList -> Loc
getNewLocForList stList =
  case M.keys stList of
    [] -> 0
    keys -> maximum keys + 1

getVarIdent :: Var -> Ident
getVarIdent (Var_T pos ident) = ident