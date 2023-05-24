module Helper where

import AbsGrammar

getIdentString :: Ident -> String
getIdentString (Ident str) = str

getArgIdent :: Arg -> Ident
getArgIdent (Arg_T _ _ ident) = ident

stringTypeOfArg :: Arg -> String
stringTypeOfArg (Arg_T _ type_ _) = case type_ of
  Int_T _ -> "int"
  CharT_T _ -> "char"
  Str_T _ -> "string"
  Bool_T _ -> "bool"

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

showBNFC :: BNFC'Position -> String
showBNFC (Just (line, col)) = "line " ++ show line ++ ", column " ++ show col
showBNFC Nothing = ""

makeError message bnfcPos = do
  let errorMessage = showBNFC bnfcPos ++ " " ++ message
  errorWithoutStackTrace errorMessage

makeTypeError message bnfcPos = do
  let errorMessage = "[type checker] " ++ showBNFC bnfcPos ++ " " ++ message
  errorWithoutStackTrace errorMessage