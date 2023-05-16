{-# LANGUAGE FlexibleContexts #-}

module Main where

import Prelude
import Data.Char ( ord, chr )
import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when )
import System.IO (hPutStrLn, stderr)
import Control.Monad.Except (MonadError, throwError)

import AbsGrammar
import LexGrammar   ( Token, mkPosToken )
import ParGrammar   ( pProgram, myLexer )
import PrintGrammar ( Print, printTree )
import SkelGrammar  ()
import Parse

import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity

type Loc = Int

type EnvVar = M.Map Ident Loc

type StoreVar = M.Map Loc (Type, ELit)

type StoreProcG = M.Map Ident ([Arg], Block)

newtype Store = Store (StoreVar, StoreProcG)

type RSE a = ReaderT EnvVar (StateT Store (ExceptT String IO)) a

showBNFC :: BNFC'Position -> String
showBNFC (Just (line, col)) = "line " ++ show line ++ ", column " ++ show col
showBNFC Nothing = ""

makeError message bnfcPos = do
  let errorMessage = showBNFC bnfcPos ++ " " ++ message
  errorWithoutStackTrace errorMessage

interpretProgram :: Program -> RSE ()
interpretProgram (Program_T _ topdefs) = do
  evalTopDefs topdefs
  evalApp BNFC'NoPosition (Ident "main") []
  return ()

evalTopDefs :: [TopDef] -> RSE ()
evalTopDefs [] = return ()
evalTopDefs (topdef : topdefs) = do
  case topdef of
    ProcDef_T pos ident args block ->
      addProcedure pos ident args block >> evalTopDefs topdefs

addProcedure :: BNFC'Position -> Ident -> [Arg] -> Block -> RSE ()
addProcedure pos ident args block = do
  store@(Store (storeVar, storeProcG)) <- get
  -- if procedure already exists, throw error
  case M.lookup ident storeProcG of
    Just _ -> makeError ("Procedure '" ++ getIdentString ident ++ "' already exists") pos
    Nothing -> do
      let newStoreProcG = M.insert ident (args, block) storeProcG
      put (Store (storeVar, newStoreProcG))

evalApp :: BNFC'Position -> Ident -> [FunArg] -> RSE ()
evalApp pos ident args = do
  if getIdentString ident == "print" then printImpl pos args else do
    if getIdentString ident == "print_line" then printLnImpl pos args else do
      (procIdent, procArgs, block, store) <- getProcedure pos ident
      (argVals, argsByVal) <- evalFunArgsAsValues pos args procArgs
      (argLocs, argsByRef) <- evalFunArgsAsRefs args procArgs
      newEnv <- bindArgsToEnv pos argsByVal argVals argsByRef argLocs
      local (const newEnv) (evalBlock block)

printImpl :: BNFC'Position -> [FunArg] -> RSE ()
printImpl pos args = do
  case args of
    [arg] -> do
      (AsValue_T pos expr) <- return arg
      val <- evalExpr expr
      case val of
        EString_T pos str -> liftIO $ putStr str
        _ -> makeError "Error: wrong argument type" pos
    _ -> makeError "Error: wrong number of arguments" pos

printLnImpl :: BNFC'Position -> [FunArg] -> RSE ()
printLnImpl pos args = do
  case args of
    [arg] -> do
      (AsValue_T pos expr) <- return arg
      val <- evalExpr expr
      case val of
        EString_T pos str -> liftIO $ putStr (str ++ "\n")
        _ -> makeError "Error: wrong argument type" pos
    _ -> makeError "Error: wrong number of arguments" pos

getProcedure :: BNFC'Position -> Ident -> RSE (Ident, [Arg], Block, Store)
getProcedure pos ident = do
  store@(Store (storeVar, storeProcG)) <- get
  case M.lookup ident storeProcG of
    Just (args, block) -> return (ident, args, block, store)
    Nothing ->
      case pos of
        BNFC'NoPosition -> makeError "There is no 'main' procedure!" pos
        _ -> makeError ("Procedure " ++ show ident ++ " does not exist") pos

storeVar :: Loc -> Type -> ELit -> RSE ()
storeVar loc ty val = do
  (Store (storeVar, storeProcG)) <- get
  let newStoreVar = M.insert loc (ty, val) storeVar
  put (Store (newStoreVar, storeProcG))

generateNewLocation :: StoreVar -> Loc
generateNewLocation storeVar =
  case M.keys storeVar of
    [] -> 0
    keys -> maximum keys + 1

evalStmts :: BNFC'Position -> [Stmt] -> RSE ()
evalStmts pos [] = return ()
evalStmts pos (stmt:stmts) = do
  case stmt of
    Decl_T pos_decl typ ident expr -> do
      evaluatedExpr <- evalExpr expr
      -- check types
      if typeOf typ == typeOfLit evaluatedExpr
        then do
          env <- ask
          (Store (storeVar, storeProcG)) <- get

          -- check if redeclaration
          case M.lookup ident env of
            Just loc -> makeError "Redeclaration of variable" pos_decl
            Nothing -> return ()

          let newLoc = generateNewLocation storeVar
          let newEnv = M.insert ident newLoc env
          let newStoreVar = M.insert newLoc (typ, evaluatedExpr) storeVar
          let newStore = Store (newStoreVar, storeProcG)

          put newStore
          local (const newEnv) (evalStmts pos stmts)
        else do
          makeError "Type mismatch" pos_decl
    _notDecl -> do
      evalStmt stmt
      evalStmts pos stmts

evalStmt :: Stmt -> RSE ()
evalStmt (Empty_T _) = return ()

evalStmt (BStmt_T _ block) = do
  evalBlock block

evalStmt (Ass_T pos ident expr) = do
  env <- ask
  Store (stVar, stProcG) <- get
  val <- evalExpr expr
  case M.lookup ident env of
    Nothing -> makeError "Type mismatch" pos
    Just loc -> do
      case M.lookup loc stVar of
        Just (t, _) ->
          if typeOf t == typeOfLit val
            then put (Store (M.insert loc (t, val) stVar, stProcG))
            else makeError "Type mismatch" pos
        Nothing -> makeError "Variable not in scope" pos
  return ()

evalStmt (App_T pos ident args) = do
  evalApp pos ident args

evalStmt (Decr_T pos ident) = do
  env <- ask
  (Store (stVar, stProcG)) <- get
  case M.lookup ident env of
    Nothing -> makeError "Type mismatch" pos
    Just loc -> do
      case M.lookup loc stVar of
        Nothing -> makeError "2. Variable not in scope" pos
        Just (t, val) -> do
          case val of
            ELitInt_T pos int -> do
              put (Store (M.insert loc (t, ELitInt_T pos (int - 1)) stVar, stProcG))
            _ -> makeError "Type mismatch" pos

evalStmt (Incr_T pos ident) = do
  env <- ask
  (Store (stVar, stProcG)) <- get
  case M.lookup ident env of
    Nothing -> makeError "Type mismatch" pos
    Just loc -> do
      case M.lookup loc stVar of
        Nothing -> makeError "4. Variable not in scope" pos
        Just (t, val) -> do
          case val of
            ELitInt_T pos int -> do
              put (Store (M.insert loc (t, ELitInt_T pos (int + 1)) stVar, stProcG))
            _ -> makeError "Type mismatch" pos

evalStmt (Cond_T pos expr block) = do
  val <- evalExpr expr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> evalBlock block
    ELitBool_T _ (ELitFalse_T _) -> return ()
    _ -> makeError "Type mismatch" pos

evalStmt (CondElse_T pos expr block1 block2) = do
  val <- evalExpr expr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> evalBlock block1
    ELitBool_T _ (ELitFalse_T _) -> evalBlock block2
    _ -> makeError "Type mismatch" pos

evalStmt (While_T pos expr block) = do
  val <- evalExpr expr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> do
      evalBlock block
      evalStmt (While_T pos expr block)
    ELitBool_T _ (ELitFalse_T _) -> return ()
    _ -> makeError "Type mismatch" pos

evalStmt (SExp_T _ expr) = undefined

evalStmt (Decl_T pos typ ident expr) = undefined

typeOfLit :: ELit -> String
typeOfLit (ELitInt_T _ _) = "Int"
typeOfLit (ELitBool_T _ _) = "Bool"
typeOfLit (EChar_T _ _) = "Char"
typeOfLit (EString_T _ _) = "String"

typeOf :: Type -> String
typeOf (Int_T _) = "Int"
typeOf (CharT_T _) = "Char"
typeOf (Str_T _) = "String"
typeOf (Bool_T _) = "Bool"

evalBlock :: Block -> RSE ()
evalBlock (Block_T pos stmts) = do
  env <- ask
  evalStmts pos stmts

argType :: Arg -> Type
argType (Arg_T _ ty _) = ty

bindArgsToEnv :: BNFC'Position -> [Arg] -> [ELit] -> [Arg] -> [Loc] -> RSE EnvVar
bindArgsToEnv _ [] [] [] [] = ask

bindArgsToEnv pos (arg : args) (val : vals) argRs locs = do
  if typeOf (argType arg) == typeOfLit val
    then do
      env <- ask
      (Store (storeVar, storeProcG)) <- get
      let newLoc = generateNewLocation storeVar
      let newEnv = M.insert (argIdent arg) newLoc env
      let newStoreVar = M.insert newLoc (argType arg, val) storeVar
      put (Store (newStoreVar, storeProcG))
      local (const newEnv) (bindArgsToEnv pos args vals argRs locs)
    else do
      makeError "Type mismatch" pos

bindArgsToEnv pos [] [] (argR : argRs) (loc : locs) = do
  env <- ask
  Store (storeVar, storeProcG) <- get
  -- check types
  case M.lookup loc storeVar of
    Nothing -> makeError "Variable not in scope" pos
    Just (t, val) ->
      if typeOf t == typeOf (argType argR)
        then do
          let newEnv = M.insert (argIdent argR) loc env
          local (const newEnv) (bindArgsToEnv pos [] [] argRs locs)
        else makeError "Type mismatch" pos

bindArgsToEnv pos _ _ _ _ = do
  makeError "Error: wrong number of arguments" pos

-- find new location
alloc :: RSE Loc
alloc = do
  (Store (stVar, storeProcG)) <- get
  return (M.size stVar)

getIdentString :: Ident -> String
getIdentString (Ident str) = str

argIdent :: Arg -> Ident
argIdent (Arg_T _ _ ident) = ident

evalFunArgsAsValues pos [] [] = return ([], [])
evalFunArgsAsValues pos args procArgs = do
  evalFunArgsAsValuesWithAcc pos args procArgs ([], [])

evalFunArgsAsValuesWithAcc :: BNFC'Position -> [FunArg] -> [Arg] -> ([ELit], [Arg]) -> RSE ([ELit], [Arg])
evalFunArgsAsValuesWithAcc pos [] [] acc = return acc
evalFunArgsAsValuesWithAcc pos (arg : args) (pArg : pArgs) (argVals, argsByVal) = do
  case arg of
    AsValue_T _ expr -> do
      val <- evalExpr expr
      evalFunArgsAsValuesWithAcc pos args pArgs (val : argVals, pArg : argsByVal)
    _ -> do
      evalFunArgsAsValuesWithAcc pos args pArgs (argVals, argsByVal)
evalFunArgsAsValuesWithAcc pos _ _ _ = do
  makeError "Error: wrong number of arguments" pos

evalFunArgsAsRefs [] [] = return ([], [])
evalFunArgsAsRefs args procArgs = do
  evalFunArgsAsRefsWithAcc args procArgs ([], [])

typeOfArg a = case a of
  Arg_T _ ty _ -> typeOf ty

evalFunArgsAsRefsWithAcc :: [FunArg] -> [Arg] -> ([Loc], [Arg]) -> RSE ([Loc], [Arg])
evalFunArgsAsRefsWithAcc [] [] acc = return acc
evalFunArgsAsRefsWithAcc (arg : args) (pArg : pArgs) (argLocs, argByLoc) = do
  Arg_T pos typArg _ <- return pArg
  case arg of
    AsRef_T _ var -> do
      ident <- evalVar var
      env <- ask
      case M.lookup ident env of
        Nothing -> makeError "Type mismatch" pos
        Just loc -> do
          evalFunArgsAsRefsWithAcc args pArgs (loc : argLocs, pArg : argByLoc)
    _ -> do
      evalFunArgsAsRefsWithAcc args pArgs (argLocs, argByLoc)
evalFunArgsAsRefsWithAcc _ _ _ = do
  makeError "Error: wrong number of arguments" BNFC'NoPosition

evalVar :: Var -> RSE Ident
evalVar (Var_T _ ident) = return ident

evalLit :: ELit -> RSE ELit
evalLit (ELitInt_T pos int) = return (ELitInt_T pos int)
evalLit (ELitBool_T pos bool) = return (ELitBool_T pos bool)
evalLit (EString_T pos str) = return (EString_T pos str)
evalLit (EChar_T pos char) = return (EChar_T pos char)

evalExpr :: Expr -> RSE ELit
evalExpr (ELit_T _ lit) = do
  evalLit lit

evalExpr (Neg_T pos expr) = do
  val <- evalExpr expr
  case val of
    ELitInt_T _ int -> return (ELitInt_T pos (- int))
    _ -> makeError "Operation not permitted" pos

evalExpr (Not_T pos expr) = do
  val <- evalExpr expr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> return (ELitBool_T pos (ELitFalse_T pos))
    ELitBool_T _ (ELitFalse_T _) -> return (ELitBool_T pos (ELitTrue_T pos))
    _ -> makeError "Operation not permitted" pos

evalExpr (EMul_T pos expr1 mulOp expr2) = do
  val1 <- evalExpr expr1
  val2 <- evalExpr expr2
  case mulOp of
    Times_T _ -> do
      case (val1, val2) of
        (ELitInt_T _ int1, ELitInt_T _ int2) -> return (ELitInt_T pos (int1 * int2))
        _ -> makeError "Operation not permitted" pos
    Div_T _ -> do
      case (val1, val2) of
        (ELitInt_T _ int1, ELitInt_T _ int2) -> do
          if int2 == 0
            then makeError "Division by zero" pos
            else
              return (ELitInt_T pos (int1 `div` int2))
        _ -> makeError "Operation not permitted" pos
    Mod_T _ -> do
      case (val1, val2) of
        (ELitInt_T _ int1, ELitInt_T _ int2) -> return (ELitInt_T pos (int1 `mod` int2))
        _ -> makeError "Operation not permitted" pos

evalExpr (EAdd_T pos expr1 addOp expr2) = do
  val1 <- evalExpr expr1
  val2 <- evalExpr expr2
  case addOp of
    Plus_T _ -> do
      case (val1, val2) of
        (ELitInt_T _ int1, ELitInt_T _ int2) -> return (ELitInt_T pos (int1 + int2))
        (EString_T _ str1, EString_T _ str2) -> return (EString_T pos (str1 ++ str2))
        _ -> makeError "Operation not permitted" pos
    Minus_T _ -> do
      case (val1, val2) of
        (ELitInt_T _ int1, ELitInt_T _ int2) -> return (ELitInt_T pos (int1 - int2))
        _ -> makeError "Operation not permitted" pos

evalExpr (EOr_T pos expr1 expr2) = do
  val1 <- evalExpr expr1
  case val1 of
    ELitBool_T _ (ELitTrue_T _) -> return (ELitBool_T pos (ELitTrue_T pos))
    ELitBool_T _ (ELitFalse_T _) -> do
      val2 <- evalExpr expr2
      case val2 of
        ELitBool_T _ (ELitTrue_T _) -> return (ELitBool_T pos (ELitTrue_T pos))
        ELitBool_T _ (ELitFalse_T _) -> return (ELitBool_T pos (ELitFalse_T pos))
        _ -> makeError "Operation not permitted" pos
    _ -> makeError "Operation not permitted" pos

evalExpr (EAnd_T pos expr1 expr2) = do
  val1 <- evalExpr expr1
  case val1 of
    ELitBool_T _ (ELitFalse_T _) -> return (ELitBool_T pos (ELitFalse_T pos))
    ELitBool_T _ (ELitTrue_T _) -> do
      val2 <- evalExpr expr2
      case val2 of
        ELitBool_T _ (ELitFalse_T _) -> return (ELitBool_T pos (ELitFalse_T pos))
        ELitBool_T _ (ELitTrue_T _) -> return (ELitBool_T pos (ELitTrue_T pos))
        _ -> makeError "Operation not permitted" pos
    _ -> makeError "Operation not permitted" pos

evalExpr (ERel_T pos expr1 relOp expr2) = do
  val1 <- evalExpr expr1
  val2 <- evalExpr expr2
  case relOp of
    LTH_T _ -> do
      case (val1, val2) of
        (ELitInt_T _ int1, ELitInt_T _ int2) -> return (ELitBool_T pos (if int1 < int2 then ELitTrue_T pos else ELitFalse_T pos))
        _ -> makeError "Operation not permitted" pos
    LE_T _ -> do
      case (val1, val2) of
        (ELitInt_T _ int1, ELitInt_T _ int2) -> return (ELitBool_T pos (if int1 <= int2 then ELitTrue_T pos else ELitFalse_T pos))
        _ -> makeError "Operation not permitted" pos
    GTH_T _ -> do
      case (val1, val2) of
        (ELitInt_T _ int1, ELitInt_T _ int2) -> return (ELitBool_T pos (if int1 > int2 then ELitTrue_T pos else ELitFalse_T pos))
        _ -> makeError "Operation not permitted" pos
    GE_T _ -> do
      case (val1, val2) of
        (ELitInt_T _ int1, ELitInt_T _ int2) -> return (ELitBool_T pos (if int1 >= int2 then ELitTrue_T pos else ELitFalse_T pos))
        _ -> makeError "Operation not permitted" pos
    EQU_T _ -> do
      case (val1, val2) of
        (ELitInt_T _ int1, ELitInt_T _ int2) -> return (ELitBool_T pos (if int1 == int2 then ELitTrue_T pos else ELitFalse_T pos))
        (ELitBool_T _ bool1, ELitBool_T _ bool2) -> return (ELitBool_T pos (if bool1 == bool2 then ELitTrue_T pos else ELitFalse_T pos))
        (EChar_T _ char1, EChar_T _ char2) -> return (ELitBool_T pos (if char1 == char2 then ELitTrue_T pos else ELitFalse_T pos))
        (EString_T _ str1, EString_T _ str2) -> return (ELitBool_T pos stringCompare)
          where stringCompare = if str1 == str2 then ELitTrue_T pos else ELitFalse_T pos
        _ -> makeError "Operation not permitted" pos
    NE_T _ -> do
      case (val1, val2) of
        (ELitInt_T _ int1, ELitInt_T _ int2) -> return (ELitBool_T pos (if int1 /= int2 then ELitTrue_T pos else ELitFalse_T pos))
        (ELitBool_T _ bool1, ELitBool_T _ bool2) -> return (ELitBool_T pos (if bool1 /= bool2 then ELitTrue_T pos else ELitFalse_T pos))
        (EChar_T _ char1, EChar_T _ char2) -> return (ELitBool_T pos (if char1 /= char2 then ELitTrue_T pos else ELitFalse_T pos))
        (EString_T _ str1, EString_T _ str2) -> return (ELitBool_T pos stringCompare)
          where stringCompare = if str1 /= str2 then ELitTrue_T pos else ELitFalse_T pos
        _ -> makeError "Operation not permitted" pos

evalExpr (ECast_T pos typ expr) = do
  val <- evalExpr expr
  case typ of
    Int_T _ -> do
      case val of
        ELitInt_T _ _ -> return val
        ELitBool_T pos (ELitTrue_T _) -> return (ELitInt_T pos 1)
        ELitBool_T pos (ELitFalse_T _) -> return (ELitInt_T pos 0)
        EChar_T pos c -> return (ELitInt_T pos (toInteger (ord c)))
        EString_T pos str -> makeError "Cannot cast string to int" pos
    CharT_T _ -> do
      case val of
        EChar_T _ _ -> return val
        ELitInt_T pos int ->
          if  int >= 0 && int <= 1114111
            then return (EChar_T pos (chr $ fromIntegral int))
            else makeError "Integer too big to convert" pos
        ELitBool_T pos _ -> makeError "Cannot cast bool to char" pos
        EString_T pos str -> makeError "Cannot cast string to char" pos
    Str_T _ -> do
      case val of
        EString_T _ _ -> return val
        ELitBool_T pos (ELitTrue_T _) -> return (EString_T pos "True")
        ELitBool_T pos (ELitFalse_T _) -> return (EString_T pos "False")
        EChar_T pos c -> return (EString_T pos [c])
        ELitInt_T pos int -> return (EString_T pos (show int))
    Bool_T _ -> do
      case val of
        ELitBool_T _ _ -> return val
        ELitInt_T pos int -> return (ELitBool_T pos
          (if int == 0 then ELitFalse_T pos else ELitTrue_T pos))
        EChar_T pos _ -> makeError "Cannot cast char to bool" pos
        EString_T pos _ -> makeError "Cannot cast string to bool" pos

evalExpr (EVar_T pos var) = do
  Var_T pos ident <- return var
  env <- ask
  Store (stVar, stProcG) <- get
  case M.lookup ident env of
    Nothing -> makeError "Variable not in scope" pos
    Just loc -> do
      case M.lookup loc stVar of
        Nothing -> makeError "Variable not in scope" pos
        Just (t, v) -> return v

initialEnv :: EnvVar
initialEnv = M.empty

printProcArg :: [Arg]
printProcArg = undefined

printBlock :: Block
printBlock = Block_T BNFC'NoPosition []

glStProc :: StoreProcG
glStProc =
  M.insert (Ident "print_line") (printProcArg, printBlock)
  (M.insert (Ident "print") (printProcArg, printBlock) M.empty)

initialStore :: Store
initialStore = Store (M.empty, glStProc)

main :: IO ()
main = do
  args <- getArgs
  p <- case args of
    []         -> getContents >>= getParsedProgram pProgram
    [fs]       -> getParsedProgramFromFile pProgram fs
    _more_args -> error "Program takes zero or one argument"

  result <- runExceptT $ runStateT (runReaderT (interpretProgram p) initialEnv) initialStore
  case result of
    Left err -> putStrLn $ "Error: " ++ err
    Right (_, _) -> return ()

