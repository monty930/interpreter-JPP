{-# LANGUAGE FlexibleContexts #-}

module Main where

import AbsGrammar
import Control.Monad (when)
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Data.Char (chr, ord)
import qualified Data.Map as M
import Helper
import LexGrammar (Token, mkPosToken)
import ParGrammar (myLexer, pProgram)
import Parse
import PrintGrammar (Print, printTree)
import SkelGrammar ()
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import TypeChecker
import Types
import Prelude

evalGenState :: BlockRetType -> GenState -> RSE (BlockReturn, GenState, EnvSt)
evalGenState ret_type [] = do
  (envSt, _envProc, _envGen) <- ask
  return (NoRet, [], envSt)

evalGenState ret_type (GenStateStmt (BStmt_T _ (Block_T _ b)) : stmts) = do
  (envSt, _envProc, _envGen) <- ask
  evalGenState ret_type (map GenStateStmt b ++ ReturnToEnv envSt : stmts)

evalGenState ret_type (GenStateStmt (Decl_T pos typ ident expr) : stmts) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  if stringTypeOfType typ == stringTypeOfElit val
    then do
      ((envVar, envIter, envList), envProc, envGen) <- ask
      (stVar, stIter, stList) <- get
      -- add variable to environment
      let newLoc = getNewLoc stVar
      put (M.insert newLoc (typ, val) stVar, stIter, stList)
      let envVar' = M.insert ident newLoc envVar
      let newEnv = ((envVar', envIter, envList), envProc, envGen)
      local (const newEnv) (evalGenState ret_type stmts)
    else do
      makeError "Type mismatch" pos

evalGenState ret_type (GenStateStmt (Yield_T pos expr) : stmts) = do
  (stVar, stIter, stList) <- get
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  (envSt, _envProc, _envGen) <- ask
  case ret_type of
    YieldType type_ -> do
      if stringTypeOfType type_ == stringTypeOfElit val
        then return (Yield val, stmts, envSt)
        else makeError "Type mismatch" pos
    _ -> makeError "Unexpected yield" pos

evalGenState ret_type (GenStateStmt (SExp_T _ expr) : stmts) = do
  evalExpr expr
  evalGenState ret_type stmts

evalGenState ret_type (GenStateStmt (Cond_T pos expr block) : stmts) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> do
      evalGenState ret_type (GenStateStmt (BStmt_T pos block) : stmts)
    ELitBool_T _ (ELitFalse_T _) -> evalGenState ret_type stmts
    _CondType -> makeError "Wrong condition type" pos

evalGenState ret_type (GenStateStmt (CondElse_T pos expr b_true b_false) : stmts) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> do
      evalGenState ret_type (GenStateStmt (BStmt_T pos b_true) : stmts)
    ELitBool_T _ (ELitFalse_T _) -> do
      evalGenState ret_type (GenStateStmt (BStmt_T pos b_false) : stmts)
    _CondType -> makeError "Wrong condition type" pos

evalGenState ret_type (GenStateStmt (Empty_T pos) : stmts) = do
  evalGenState ret_type stmts

evalGenState ret_type (GenStateStmt (While_T pos expr block) : stmts) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> do
      evalGenState ret_type (
        GenStateStmt (BStmt_T pos block) :
        GenStateStmt (While_T pos expr block) :
        stmts)
    ELitBool_T _ (ELitFalse_T _) -> evalGenState ret_type stmts
    _CondType -> makeError "Wrong condition type" pos

evalGenState ret_type (GenStateStmt (Return_T pos expr) : _) = do
  makeError "Return statement outside procedure" pos

evalGenState ret_type (GenStateStmt (DeclGen_T pos ident1 ident2 funargs) : stmts) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get

  case M.lookup ident2 envGen of
    Just (type_, args, block, envSt) -> do
      let wholeEnv = (envSt, envProc, envGen)
      (envSt', _, _) <- addArgsToEnvGen pos wholeEnv args funargs
      let newLoc = getNewLocForGen stIter
      let envIter' = M.insert ident1 newLoc envIter
      let newEnv = ((envVar, envIter', envList), envProc, envGen)
      (stVar, stIter, stList) <- get
      put (stVar,
        M.insert newLoc
          (type_,
          [GenStateStmt (BStmt_T BNFC'NoPosition block)],
          envSt')
          stIter, stList)
      local (const newEnv) (evalGenState ret_type stmts)
    Nothing -> do
      makeError "Generator not implemented yet" pos

evalGenState ret_type (GenStateStmt (Incr_T pos ident) : stmts) = do
  modifyVariable pos ident (+ 1)
  evalGenState ret_type stmts

evalGenState ret_type (GenStateStmt (Decr_T pos ident) : stmts) = do
  modifyVariable pos ident (\x -> x - 1)
  evalGenState ret_type stmts

evalGenState ret_type (GenStateStmt (Ass_T pos ident expr) : stmts) = do
  ((envVar, _envIter, _envList), _envProc, _envGen) <- ask
  (stVar, stIter, stList) <- get
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case M.lookup ident envVar of
    Nothing -> makeError "Variable not in scope" pos
    Just loc -> do
      case M.lookup loc stVar of
        Just (typ, _) ->
          if stringTypeOfType typ == stringTypeOfElit val
            then do
              (stVar, stIter, stList) <- get
              put (M.insert loc (typ, val) stVar, stIter, stList)
              evalGenState ret_type stmts
            else makeError "Type mismatch" pos
        Nothing -> makeError "Variable not in scope" pos

evalGenState ret_type (GenStateStmt (ForGen_T pos ident1 ident2 funargs for_body) : stmts) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  case M.lookup ident2 envGen of
    Nothing -> do
      makeError "Generator not implemented yet" pos
    Just (type_, args, block, envSt) -> do
      let newLoc = getNewLoc stVar
      (stVar, stIter, stList) <- get
      let newStVar = M.insert newLoc (defaultValue type_) stVar
      put (newStVar, stIter, stList)
      (envSt', _, _) <- addArgsToEnvGen pos (envSt, envProc, envGen) args funargs
      let envVar' = M.insert ident1 newLoc envVar
      let newEnvSt = (envVar', envIter, envList)
      let wholeEnv = (newEnvSt, envProc, envGen)
      let forInfo = (type_, newLoc, [GenStateStmt (BStmt_T BNFC'NoPosition block)], envSt', for_body)
      local (const wholeEnv) (evalGenState ret_type (ForInfo forInfo : stmts))

evalGenState ret_type (ForInfo (type_, loc, gState, envSt, for_body) : stmts) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  (ret, gSt, env') <- evalGenNextFor type_ gState envSt
  (stVar', stIter, stList) <- get
  put (M.insert loc (type_, blockRetToElit ret) stVar', stIter, stList)
  case ret of
    NoRet -> evalGenState ret_type stmts
    _ -> do
      let newForInfo = (type_, loc, gSt, env', for_body)
      evalGenState ret_type (GenStateStmt (BStmt_T BNFC'NoPosition for_body) : ForInfo newForInfo : stmts)

evalGenState ret_type (GenStateStmt (Break_T pos) : stmts) = do
  let stmts' = removeWhileFromStack pos stmts
  evalGenState ret_type stmts'

evalGenState ret_type (GenStateStmt (Continue_T pos) : stmts) = do
  let stmts' = removeRestOfBlockFromStack pos stmts
  evalGenState ret_type stmts'

evalGenState ret_type (ReturnToEnv e : stmts) = do
  (_, envProc, envGen) <- ask
  let newEnv = (e, envProc, envGen)
  local (const newEnv) (evalGenState ret_type stmts)

evalGenState ret_type (GenStateStmt (PushToList_T pos ident expr) : stmts) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case M.lookup ident envList of
    Nothing -> makeError "List variable not in scope" pos
    Just loc -> do
      case M.lookup loc stList of
        Nothing -> makeError "List variable not in scope" pos
        Just (type_, list) -> do
          if stringTypeOfType type_ == stringTypeOfElit val
            then do
              let newList = list ++ [val]
              put (stVar, stIter, M.insert loc (type_, newList) stList)
              evalGenState ret_type stmts
            else makeError "Type mismatch" pos

evalGenState ret_type (GenStateStmt (PopFromList_T pos ident) : stmts) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  case M.lookup ident envList of
    Nothing -> makeError "List variable not in scope" pos
    Just loc -> do
      case M.lookup loc stList of
        Nothing -> makeError "List variable not in scope" pos
        Just (type_, list) -> do
          if null list
            then makeError "Empty list" pos
            else do
              let newList = init list
              put (stVar, stIter, M.insert loc (type_, newList) stList)
              evalGenState ret_type stmts

evalGenState ret_type (GenStateStmt (AddToList_T pos ident expr1 expr2) : stmts) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  retFromExpr1 <- evalExpr expr1
  elitID <- getValFromExpr retFromExpr1
  id <- getIntegerFromId pos elitID
  retFromExpr2 <- evalExpr expr2
  val <- getValFromExpr retFromExpr2
  case M.lookup ident envList of
    Nothing -> makeError "List variable not in scope" pos
    Just loc -> do
      case M.lookup loc stList of
        Nothing -> makeError "List variable not in scope" pos
        Just (type_, list) -> do
          if stringTypeOfType type_ == stringTypeOfElit val
            then do
              newList <- putInList pos list id val
              put (stVar, stIter, M.insert loc (type_, newList) stList)
              evalGenState ret_type stmts
            else makeError "Type mismatch" pos

evalGenState ret_type (GenStateStmt (RemoveFromList_T pos ident expr) : stmts) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  retFromExpr <- evalExpr expr
  idElit <- getValFromExpr retFromExpr
  id <- getIntegerFromId pos idElit
  case M.lookup ident envList of
    Nothing -> makeError "List variable not in scope" pos
    Just loc -> do
      case M.lookup loc stList of
        Nothing -> makeError "List variable not in scope" pos
        Just (type_, list) -> do
          let newList = removeFromList list id
          put (stVar, stIter, M.insert loc (type_, newList) stList)
          evalGenState ret_type stmts

evalGenState ret_type (GenStateStmt (DeclList_T pos type_ ident exprs) : stmts) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  let newLoc = getNewLocForList stList
  list <- listOfExprs pos [] exprs type_
  put (stVar, stIter, M.insert newLoc (type_, list) stList)
  let envList' = M.insert ident newLoc envList
  let newEnv = ((envVar, envIter, envList'), envProc, envGen)
  local (const newEnv) (evalGenState ret_type stmts)

listOfExprs :: BNFC'Position -> [ELit] -> [Expr] -> Type -> RSE [ELit]
listOfExprs pos acc [] type_ = return acc

listOfExprs pos acc (ex : exs) type_ = do
  retFromExpr <- evalExpr ex
  val <- getValFromExpr retFromExpr
  if stringTypeOfType type_ == stringTypeOfElit val
    then do
      listOfExprs pos (acc ++ [val]) exs type_
    else do
      makeError "Type mismatch" pos

removeFromList :: [ELit] -> Integer -> [ELit]
removeFromList list id = do
  let (before, after) = splitAt (fromIntegral id) list
  before ++ tail after

getIntegerFromId :: BNFC'Position -> ELit -> RSE Integer
getIntegerFromId _ (ELitInt_T _ int) = return int
getIntegerFromId pos _ = makeError "Wrong type" BNFC'NoPosition

putInList :: BNFC'Position -> [ELit] -> Integer -> ELit -> RSE [ELit]
putInList pos list id val = do
  valAtId <- getFromList pos list id
  let (before, after) = splitAt (fromIntegral id) list
  return (before ++ [val] ++ [valAtId] ++ tail after)

removeRestOfBlockFromStack :: BNFC'Position -> GenState -> GenState
removeRestOfBlockFromStack pos stmts@(ReturnToEnv e : GenStateStmt While_T {} : _) = stmts

removeRestOfBlockFromStack pos (stmt : stmts) = removeRestOfBlockFromStack pos stmts

removeRestOfBlockFromStack pos _ = makeError "Continue outside while" pos

removeWhileFromStack ::  BNFC'Position -> GenState -> GenState
removeWhileFromStack pos (ReturnToEnv e : GenStateStmt While_T {} : stmts) = stmts

removeWhileFromStack pos (stmt : stmts) = removeWhileFromStack pos stmts

removeWhileFromStack pos _ = makeError "Break outside while" pos

addArgsToEnvGen :: BNFC'Position -> Env -> [Arg] -> [FunArg] -> RSE Env
addArgsToEnvGen pos env [] [] = return env

-- args: what generator wants, funargs: what we get
addArgsToEnvGen pos env (arg : args) (funarg : funargs) = do
  ((envVar, envIter, envSt), envProc, envGen) <- ask
  case funarg of
    AsValue_T pos expr -> do
      retFromExpr <- evalExpr expr
      val <- getValFromExpr retFromExpr
      if stringTypeOfArg arg == stringTypeOfElit val
        then do
          (stVar, stIter, stList) <- get
          let newLoc = getNewLoc stVar
          put (M.insert newLoc (typeOfArg arg, val) stVar, stIter, stList)
          let ((envVar, envIter, envList), envProc, envGen) = env
          let envVar' = M.insert (getArgIdent arg) newLoc envVar
          let env' = ((envVar', envIter, envList), envProc, envGen)
          addArgsToEnvGen pos env' args funargs
        else do
          makeError "Wrong argument type" pos
    AsRef_T pos var -> do
      (stVar, _stIter, _stList) <- get
      ((envVar, envIter, envList), envProc, envGen) <- ask
      case M.lookup (identOfVar var) envVar of
        Just loc -> do
          case M.lookup loc stVar of
            Just (type_, _) -> do
              if stringTypeOfArg arg == stringTypeOfType type_
                then do
                  let ((envVar, envIter, envList), envProc, envGen) = env
                  let envVar' = M.insert (getArgIdent arg) loc envVar
                  let env' = ((envVar', envIter, envList), envProc, envGen)
                  addArgsToEnvGen pos env' args funargs
                else do
                  makeError "Wrong argument type" pos
            Nothing -> do
              makeError "Variable not in scope" pos
        Nothing -> do
          makeError "Variable not in scope" pos

addArgsToEnvGen pos _ _ _ = do
  makeError "Wrong number of arguments" pos

identOfVar :: Var -> Ident
identOfVar (Var_T _ ident) = ident

interpretProgram :: Program -> RSE ()
interpretProgram (Program_T _ topdefs) = do
  env <- evalTopDefs topdefs
  _ <- local (const env) (evalApp BNFC'NoPosition (Ident "main") [])
  return ()

evalTopDefs :: [TopDef] -> RSE Env
evalTopDefs [] = ask
evalTopDefs (topdef : topdefs) = do
  case topdef of
    ProcDecl_T pos ret ident args -> do
      (envSt, envProc, envGen) <- ask
      -- check if procedure is already defined
      case M.lookup ident envProc of
        Just _ -> makeError ("Procedure " ++ getIdentString ident ++ " already defined") pos
        Nothing -> do
          -- add procedure to environment
          let emptyBlock = Block_T BNFC'NoPosition []
          let envProc' = M.insert ident (ret, args, emptyBlock, envSt, False) envProc
          let newEnv = (envSt, envProc', envGen)
          local (const newEnv) (evalTopDefs topdefs)

    ProcDef_T pos ret ident args block -> do
      (envSt, envProc, envGen) <- ask
      -- check if procedure is already defined
      case M.lookup ident envProc of
        Just (_, _, _, _, True) -> makeError ("Procedure " ++ getIdentString ident ++ " already defined") pos
        _ -> do
          -- add procedure to environment
          let envProc' = M.insert ident (ret, args, block, envSt, True) envProc
          let newEnv = (envSt, envProc', envGen)
          local (const newEnv) (evalTopDefs topdefs)

    GlobVar_T pos type_ ident expr -> do
      ((envVar, envIter, envList), envProc, envGen) <- ask
      (stVar, stIter, stList) <- get
      retFromExpr <- evalExpr expr
      val <- getValFromExpr retFromExpr
      -- check types
      if stringTypeOfType type_ == stringTypeOfElit val
        then do
          -- add variable to environment
          let newLoc = getNewLoc stVar
          put (M.insert newLoc (type_, val) stVar, stIter, stList)
          let envVar' = M.insert ident newLoc envVar
          let newEnv = ((envVar', envIter, envList), envProc, envGen)
          local (const newEnv) (evalTopDefs topdefs)
        else do
          makeError "Type mismatch" pos

    ListGlobDecl_T pos type_ ident exprs -> do
      ((envVar, envIter, envList), envProc, envGen) <- ask
      (stVar, stIter, stList) <- get
      let newLoc = getNewLocForList stList
      list <- listOfExprs pos [] exprs type_
      put (stVar, stIter, M.insert newLoc (type_, list) stList)
      let envList' = M.insert ident newLoc envList
      let newEnv = ((envVar, envIter, envList'), envProc, envGen)
      local (const newEnv) (evalTopDefs topdefs)
      
    Gener_T pos type_ ident args block -> do
      (envSt, envProc, envGen) <- ask
      -- check if generator is already defined
      case M.lookup ident envGen of
        Just _ -> makeError ("Generator " ++ getIdentString ident ++ " already defined!") pos
        Nothing -> do
          -- add generator to environment
          let envGen' = M.insert ident (type_, args, block, envSt) envGen
          let newEnv = (envSt, envProc, envGen')
          local (const newEnv) (evalTopDefs topdefs)

bindArgsToEnv :: BNFC'Position -> [Arg] -> [ELit] -> [Arg] -> [Loc] -> EnvVar -> RSE EnvVar

bindArgsToEnv _ [] [] [] [] envVar = return envVar

bindArgsToEnv pos (arg : args) (val : vals) refs locs envVar = do
  if stringTypeOfArg arg == stringTypeOfElit val
    then do
      (stVar, stIter, stList) <- get
      let newLoc = getNewLoc stVar
      put (M.insert newLoc (typeOfArg arg, val) stVar, stIter, stList)
      let envVar' = M.insert (getArgIdent arg) newLoc envVar
      ((_, envIter, envList), envProc, envGen) <- ask
      let newEnv = ((envVar', envIter, envList), envProc, envGen)
      local (const newEnv) (bindArgsToEnv pos args vals refs locs envVar')
    else do
      makeError "Wrong argument type" pos

bindArgsToEnv pos args vals (ref : refs) (loc : locs) envVar = do
  (stVar, _stIter, _stList) <- get
  ((_, envIter, envList), envProc, envGen) <- ask
  case M.lookup loc stVar of
    Just (type_, _) -> do
      if stringTypeOfArg ref == stringTypeOfType type_
        then do
          let envVar' = M.insert (getArgIdent ref) loc envVar
          let newEnv = ((envVar', envIter, envList), envProc, envGen)
          local (const newEnv) (bindArgsToEnv pos args vals refs locs envVar')
        else do
          makeError "Wrong argument type" pos
    Nothing -> do
      makeError "Variable not in scope" pos

bindArgsToEnv pos _ _ _ _ _ = do
  error "Wrong number of arguments" pos

evalApp :: BNFC'Position -> Ident -> [FunArg] -> RSE BlockReturn
evalApp pos ident args = do
  if getIdentString ident == "print"
    then printImpl pos args
    else do
      if getIdentString ident == "print_line"
        then printLnImpl pos args
        else do
          ((envVar, envIter, envList), envProc, envGen) <- ask
          (ret, args', block, (envVar', envIter', envList'), _defined) <- case M.lookup ident envProc of
            Just (ret, args', block, (envVar', envIter', envList'), True) -> return (ret, args', block, (envVar', envIter', envList'), True)
            Just (_, _, _, _, False) -> makeError ("Procedure " ++ getIdentString ident ++ " not defined") pos
            Nothing ->
              case pos of
                BNFC'NoPosition -> makeError "There is no 'main' procedure!" pos
                _ -> makeError ("Procedure " ++ getIdentString ident ++ " does not exist") pos
          (argVals, argsByVal) <- evalFunArgsAsValues pos args args'
          (argLocs, argsByRef) <- evalFunArgsAsRefs pos args args'
          newEnvVar <- bindArgsToEnv pos argsByVal argVals argsByRef argLocs envVar'
          let newEnv = ((newEnvVar, envIter', envList'), envProc, envGen)
          ret_type <- if stringFunctionType ret == "void"
            then return NoRetType
            else return (RetType (typeOfRetVal ret))
          returned <- local (const newEnv) (evalBlock ret_type block)
          case returned of
            Ret val -> do
              if stringTypeOfElit val == stringFunctionType ret
                then return (Ret val)
                else makeError "Wrong return type" pos
            NoRet -> do
              if stringFunctionType ret == "void"
                then return NoRet
                else makeError "Missing return statement" pos
            Yield val -> do
              makeError "Yield statement outside generator" pos
            _ -> undefined -- intended

typeOfRetVal :: RetVal -> Type
typeOfRetVal (FunRetVal_T _ type_) = type_
typeOfRetVal (FunRetVoid_T _) = undefined -- intended

evalFunArgsAsValues :: BNFC'Position -> [FunArg] -> [Arg] -> RSE ([ELit], [Arg])
evalFunArgsAsValues pos args idfs = do
  evalFunArgsAsValuesAcc pos args idfs ([], [])

evalFunArgsAsValuesAcc :: BNFC'Position -> [FunArg] -> [Arg] -> ([ELit], [Arg]) -> RSE ([ELit], [Arg])
evalFunArgsAsValuesAcc pos [] [] acc = return acc
evalFunArgsAsValuesAcc pos (arg : args) (idf : idfs) (argVals, argsByVal) = do
  case arg of
    AsValue_T pos expr -> do
      retFromExpr <- evalExpr expr
      val <- getValFromExpr retFromExpr
      evalFunArgsAsValuesAcc pos args idfs (argVals ++ [val], argsByVal ++ [idf])
    AsRef_T pos var -> do
      evalFunArgsAsValuesAcc pos args idfs (argVals, argsByVal)
evalFunArgsAsValuesAcc pos _ _ _ = do
  makeError "Wrong number of arguments" pos

evalFunArgsAsRefs :: BNFC'Position -> [FunArg] -> [Arg] -> RSE ([Loc], [Arg])
evalFunArgsAsRefs pos args idfs = do
  evalFunArgsAsRefsAcc pos args idfs ([], [])

evalFunArgsAsRefsAcc :: BNFC'Position -> [FunArg] -> [Arg] -> ([Loc], [Arg]) -> RSE ([Loc], [Arg])
evalFunArgsAsRefsAcc _ [] [] acc = return acc
evalFunArgsAsRefsAcc pos (arg : args) (idf : idfs) (argLocs, argsByRef) = do
  case arg of
    AsValue_T pos expr -> do
      evalFunArgsAsRefsAcc pos args idfs (argLocs, argsByRef)
    AsRef_T pos var -> do
      loc <- evalVar var
      evalFunArgsAsRefsAcc pos args idfs (argLocs ++ [loc], argsByRef ++ [idf])
evalFunArgsAsRefsAcc pos _ _ _ = do
  error "Wrong number of arguments" pos

printImpl :: BNFC'Position -> [FunArg] -> RSE BlockReturn
printImpl pos args = do
  case args of
    [arg] -> do
      (AsValue_T pos expr) <- return arg
      retFromExpr <- evalExpr expr
      val <- getValFromExpr retFromExpr
      case val of
        EString_T pos str -> do
          liftIO $ putStr str
          return NoRet
        _ -> makeError "Wrong argument type" pos
    _ -> makeError "Wrong number of arguments" pos

printLnImpl :: BNFC'Position -> [FunArg] -> RSE BlockReturn
printLnImpl pos args = do
  case args of
    [arg] -> do
      (AsValue_T pos expr) <- return arg
      retFromExpr <- evalExpr expr
      val <- getValFromExpr retFromExpr
      case val of
        EString_T pos str -> do
          liftIO $ putStr (str ++ "\n")
          return NoRet
        _ -> makeError "Wrong argument type" pos
    _ -> makeError "Wrong number of arguments" pos

evalGenNext :: BNFC'Position -> Ident -> RSE BlockReturn
evalGenNext pos varIdent = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  case M.lookup varIdent envIter of
    Nothing -> makeError ("Generator variable " ++ getIdentString varIdent ++ " not in scope") pos
    Just loc -> do
      case M.lookup loc stIter of
        Nothing -> makeError ("Generator variable " ++ getIdentString varIdent ++ " not in scope") pos
        Just (type_, genState, envSt) -> do
          let newEnv = (envSt, envProc, envGen)
          (ret, genState', envSt') <-
            local (const newEnv) (evalGenState (YieldType type_) genState)
          (stVar, stIter, stList) <- get
          put (stVar, M.insert loc (type_, genState', envSt') stIter, stList)
          return ret

evalBlock :: BlockRetType -> Block -> RSE BlockReturn
evalBlock ret_type (Block_T pos stmts) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  evalStmts ret_type pos stmts

evalStmts :: BlockRetType -> BNFC'Position -> [Stmt] -> RSE BlockReturn
evalStmts NoRetType _ [] = return NoRet
evalStmts ret_type pos (stmt : stmts) = do
  case stmt of
    DeclGen_T pos_decl identVar identGen args -> do
      ((envVar, envIter, envList), envProc, envGen) <- ask
      (stVar, stIter, stList) <- get
      case M.lookup identGen envGen of
        Just (type_, args', block, envSt) -> do
          let wholeEnv = (envSt, envProc, envGen)
          (envSt', _, _) <- addArgsToEnvGen pos wholeEnv args' args
          (stVar, stIter, stList) <- get
          let newLoc = getNewLocForGen stIter
          put (
            stVar,
            M.insert
              newLoc
              (type_, [GenStateStmt (BStmt_T BNFC'NoPosition block)], envSt')
              stIter, stList)
          let envIter' = M.insert identVar newLoc envIter
          let newEnv = ((envVar, envIter', envList), envProc, envGen)
          local (const newEnv) (evalStmts ret_type pos stmts)
        Nothing -> do
          makeError ("Generator " ++ show identGen ++ " not implemented") pos_decl
    Decl_T pos_decl typ ident expr -> do
      retFromExpr <- evalExpr expr
      evaluatedExpr <- getValFromExpr retFromExpr
      if stringTypeOfType typ == stringTypeOfElit evaluatedExpr
        then do
          ((envVar, envIter, envList), envProc, envGen) <- ask
          (stVar, stIter, stList) <- get

          -- add variable to environment
          let newLoc = getNewLoc stVar
          put (M.insert newLoc (typ, evaluatedExpr) stVar, stIter, stList)
          let envVar' = M.insert ident newLoc envVar
          let newEnv = ((envVar', envIter, envList), envProc, envGen)
          local (const newEnv) (evalStmts ret_type pos stmts)
        else do
          makeError "Type mismatch" pos_decl
    DeclList_T pos_decl type_ ident exprs -> do
      ((envVar, envIter, envList), envProc, envGen) <- ask
      (stVar, stIter, stList) <- get
      let newLoc = getNewLocForList stList
      list <- listOfExprs pos_decl [] exprs type_
      put (stVar, stIter, M.insert newLoc (type_, list) stList)
      let envList' = M.insert ident newLoc envList
      let newEnv = ((envVar, envIter, envList'), envProc, envGen)
      local (const newEnv) (evalStmts ret_type pos stmts)
    _notDecl -> do
      ret <- evalStmt ret_type stmt
      case ret of
        Ret val -> return (Ret val)
        Yield val -> return (Yield val)
        Break -> return Break
        Continue -> return Continue
        NoRet -> evalStmts ret_type pos stmts

evalStmts _ pos [] = return NoRet

evalStmt :: BlockRetType -> Stmt -> RSE BlockReturn
evalStmt _ (Empty_T _) = return NoRet

evalStmt ret_type (BStmt_T _ block) = do
  evalBlock ret_type block

evalStmt _ Decl_T {} = undefined -- intended: declaration handled in evalStmts

evalStmt _ (Decr_T pos ident) = do
  modifyVariable pos ident (\x -> x - 1)
  return NoRet

evalStmt _ (Incr_T pos ident) = do
  modifyVariable pos ident (+ 1)
  return NoRet

evalStmt ret_type (Cond_T pos expr block) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> evalBlock ret_type block
    ELitBool_T _ (ELitFalse_T _) -> return NoRet
    _CondType -> makeError "Wrong condition type" pos

evalStmt ret_type (CondElse_T pos expr block1 block2) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> evalBlock ret_type block1
    ELitBool_T _ (ELitFalse_T _) -> evalBlock ret_type block2
    _CondType -> makeError "Wrong condition type" pos

evalStmt ret_type (While_T pos expr block) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> do
      ret <- evalBlock ret_type block
      case ret of
        Ret val -> return (Ret val)
        Yield val -> return (Yield val)
        Break -> return NoRet
        _ -> evalStmt ret_type (While_T pos expr block) -- no return or continue
    ELitBool_T _ (ELitFalse_T _) -> return NoRet
    _CondType -> makeError "Wrong condition type" pos

evalStmt _ (Ass_T pos ident expr) = do
  ((envVar, _envIter, _envList), _envProc, _envGen) <- ask
  (stVar, stIter, stList) <- get
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case M.lookup ident envVar of
    Nothing -> makeError "Variable not in scope" pos
    Just loc -> do
      case M.lookup loc stVar of
        Just (typ, _) ->
          if stringTypeOfType typ == stringTypeOfElit val
            then do
              put (M.insert loc (typ, val) stVar, stIter, stList)
            else makeError "Type mismatch" pos
        Nothing -> makeError "Variable not in scope" pos
  return NoRet

evalStmt (RetType type_) (Return_T pos expr) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  return (Ret val)

evalStmt _ (Return_T pos _) = do
  makeError "Unexpected return" pos

evalStmt _ (SExp_T _ expr) = do
  evalExpr expr
  return NoRet

evalStmt _ (Yield_T pos expr) = do
  makeError "Unexpected yield" pos

evalStmt _ (DeclGen_T pos var gen args) = undefined -- intended: declaration handled in evalStmts

evalStmt ret_type (ForGen_T pos identVar identGen args for_body) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  case M.lookup identGen envGen of
    Nothing -> do
      makeError "Generator not implemented yet" pos
    Just (type_, args', block, envSt) -> do
      -- add variable to environment
      let newLoc = getNewLoc stVar
      let newStVar = M.insert newLoc (defaultValue type_) stVar
      put (newStVar, stIter, stList)
      let envVarForBlock = M.insert identVar newLoc envVar
      let envForBlock = (envVarForBlock, envIter, envList)
      evalFor
        ret_type
        newLoc
        type_
        [GenStateStmt (BStmt_T BNFC'NoPosition block)]
        envSt
        envForBlock
        for_body

evalStmt ret_type (Break_T pos) = do
  return Break

evalStmt ret_type (Continue_T pos) = do
  return Continue

evalStmt ret_type DeclList_T {} = undefined -- intended

evalStmt ret_type (PushToList_T pos ident expr) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case M.lookup ident envList of
    Nothing -> makeError "List variable not in scope" pos
    Just loc -> do
      case M.lookup loc stList of
        Nothing -> makeError "List variable not in scope" pos
        Just (type_, list) -> do
          if stringTypeOfType type_ == stringTypeOfElit val
            then do
              let newList = list ++ [val]
              put (stVar, stIter, M.insert loc (type_, newList) stList)
              return NoRet
            else makeError "Type mismatch" pos

evalStmt ret_type (PopFromList_T pos ident) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  case M.lookup ident envList of
    Nothing -> makeError "List variable not in scope" pos
    Just loc -> do
      case M.lookup loc stList of
        Nothing -> makeError "List variable not in scope" pos
        Just (type_, list) -> do
          if not (null list)
            then do
              let newList = init list
              put (stVar, stIter, M.insert loc (type_, newList) stList)
              return NoRet
            else makeError "List is empty" pos

evalStmt ret_type (RemoveFromList_T pos ident expr) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  retFromExpr <- evalExpr expr
  idElit <- getValFromExpr retFromExpr
  id <- getIntegerFromId pos idElit
  case M.lookup ident envList of
    Nothing -> makeError "List variable not in scope" pos
    Just loc -> do
      case M.lookup loc stList of
        Nothing -> makeError "List variable not in scope" pos
        Just (type_, list) -> do
          let newList = removeFromList list id
          put (stVar, stIter, M.insert loc (type_, newList) stList)
          return NoRet

evalStmt ret_type (AddToList_T pos ident expr1 expr2) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  retFromExpr1 <- evalExpr expr1
  idElit <- getValFromExpr retFromExpr1
  id <- getIntegerFromId pos idElit
  retFromExpr2 <- evalExpr expr2
  val <- getValFromExpr retFromExpr2
  case M.lookup ident envList of
    Nothing -> makeError "List variable not in scope" pos
    Just loc -> do
      case M.lookup loc stList of
        Nothing -> makeError "List variable not in scope" pos
        Just (type_, list) -> do
          newList <- putInList pos list id val
          put (stVar, stIter, M.insert loc (type_, newList) stList)
          return NoRet

blockRetToElit :: BlockReturn -> ELit
blockRetToElit (Yield val) = val
blockRetToElit (Ret val) = undefined -- intended
blockRetToElit NoRet = undefined -- intended
blockRetToElit Break = undefined -- intended
blockRetToElit Continue = undefined -- intended

evalFor :: BlockRetType -> Loc -> Type -> GenState -> EnvSt -> EnvSt -> Block -> RSE BlockReturn
evalFor ret_type loc type_ gState env envForBlock block = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  (ret, gSt, env') <- evalGenNextFor type_ gState env
  (stVar', stIter', stList') <- get
  put (M.insert loc (type_, blockRetToElit ret) stVar', stIter', stList')
  case ret of
    NoRet -> do
      return NoRet
    _ -> do
      ret_from_block <- local (const (envForBlock, envProc, envGen)) (evalBlock ret_type block)
      case ret_from_block of
        Ret val -> do
          return (Ret val)
        Yield val -> do
          makeError "Yield statement outside generator" BNFC'NoPosition
        Break -> do
          return Break
        Continue -> do
          return Continue
        NoRet -> do
          evalFor ret_type loc type_ gSt env' envForBlock block

evalGenNextFor :: Type -> GenState -> EnvSt -> RSE (BlockReturn, GenState, EnvSt)
evalGenNextFor type_ gState envSt = do
  (_envSt, envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  let newEnv = (envSt, envProc, envGen)
  res@(ret, genState', envSt') <- local (const newEnv) (evalGenState (YieldType type_) gState)
  return res

defaultValue :: Type -> (Type, ELit)
defaultValue type_ =
  case type_ of
    Int_T _ -> (type_, ELitInt_T BNFC'NoPosition 0)
    Bool_T _ -> (type_, ELitBool_T BNFC'NoPosition (ELitFalse_T BNFC'NoPosition))
    Str_T _ -> (type_, EString_T BNFC'NoPosition "")
    _ -> undefined -- intended

modifyVariable :: BNFC'Position -> Ident -> (Integer -> Integer) -> RSE ()
modifyVariable pos ident modifyFn = do
  (stVar, stIter, stList) <- get
  ((envVar, _envIter, _envList), _envProc, _envGen) <- ask
  case M.lookup ident envVar of
    Nothing -> makeError ("Variable " ++ getIdentString ident ++ " not in scope") pos
    Just loc -> do
      case M.lookup loc stVar of
        Nothing -> makeError ("Variable " ++ getIdentString ident ++ " not in scope") pos
        Just (type_, val) -> do
          case val of
            ELitInt_T pos val' -> do
              put (M.insert loc (type_, ELitInt_T pos (modifyFn val')) stVar, stIter, stList)
            _ -> makeError ("Variable " ++ getIdentString ident ++ " is not an integer") pos

evalVar :: Var -> RSE Loc
evalVar (Var_T pos ident) = do
  ((envVar, _envIter, _envSt), _envProc, envGen) <- ask
  case M.lookup ident envVar of
    Nothing -> do
      makeError ("Variable " ++ getIdentString ident ++ " not in scope") pos
    Just loc -> return loc

getValFromExpr :: BlockReturn -> RSE ELit
getValFromExpr (Ret val) = do
  return val
getValFromExpr (Yield val) = do
  return val
getValFromExpr _ = makeError "No return value" BNFC'NoPosition

evalExpr :: Expr -> RSE BlockReturn
evalExpr (EVar_T pos var) = do
  loc <- evalVar var
  (stVar, _stIter, _stList) <- get
  case M.lookup loc stVar of
    Nothing -> makeError "Variable not in scope" pos
    Just (_, val) -> return (Ret val)
evalExpr (ELit_T _ lit) = return (Ret lit)
evalExpr (Neg_T pos expr) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case val of
    ELitInt_T _ val -> return (Ret (ELitInt_T pos (- val)))
    _ -> makeError "Wrong operation argument" pos
evalExpr (Not_T pos expr) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> return (Ret (ELitBool_T pos (ELitFalse_T pos)))
    ELitBool_T _ (ELitFalse_T _) -> return (Ret (ELitBool_T pos (ELitTrue_T pos)))
    _ -> makeError "Wrong operation argument" pos
evalExpr (EMul_T pos expr1 mulOp expr2) = do
  retFromExpr1 <- evalExpr expr1
  val1 <- getValFromExpr retFromExpr1
  retFromExpr2 <- evalExpr expr2
  val2 <- getValFromExpr retFromExpr2
  case (val1, val2) of
    (ELitInt_T _ val1', ELitInt_T _ val2') -> do
      case mulOp of
        Times_T _ -> return (Ret (ELitInt_T pos (val1' * val2')))
        Div_T _ -> do
          if val2' == 0
            then makeError "Division by zero" pos
            else return (Ret (ELitInt_T pos (val1' `div` val2')))
        Mod_T _ -> return (Ret (ELitInt_T pos (val1' `mod` val2')))
    _ -> makeError "Wrong operation argument" pos
evalExpr (EAdd_T pos expr1 addOp expr2) = do
  retFromExpr1 <- evalExpr expr1
  val1 <- getValFromExpr retFromExpr1
  retFromExpr2 <- evalExpr expr2
  val2 <- getValFromExpr retFromExpr2
  case (val1, val2) of
    (ELitInt_T _ val1', ELitInt_T _ val2') -> do
      case addOp of
        Plus_T _ -> return (Ret (ELitInt_T pos (val1' + val2')))
        Minus_T _ -> return (Ret (ELitInt_T pos (val1' - val2')))
    (EString_T _ val1', EString_T _ val2') -> do
      case addOp of
        Plus_T _ -> return (Ret (EString_T pos (val1' ++ val2')))
        _ -> makeError "Wrong operation argument" pos
    _ -> makeError "Wrong operation argument" pos
evalExpr (EOr_T pos expr1 expr2) = do
  retFromExpr1 <- evalExpr expr1
  val1 <- getValFromExpr retFromExpr1
  case val1 of
    ELitBool_T _ (ELitTrue_T _) -> return (Ret (ELitBool_T pos (ELitTrue_T pos)))
    ELitBool_T _ (ELitFalse_T _) -> do
      retFromExpr2 <- evalExpr expr2
      val2 <- getValFromExpr retFromExpr2
      case val2 of
        ELitBool_T _ (ELitTrue_T _) -> return (Ret (ELitBool_T pos (ELitTrue_T pos)))
        ELitBool_T _ (ELitFalse_T _) -> return (Ret (ELitBool_T pos (ELitFalse_T pos)))
        _ -> makeError "Wrong operation argument" pos
    _ -> makeError "Wrong operation argument" pos
evalExpr (EAnd_T pos expr1 expr2) = do
  retFromExpr1 <- evalExpr expr1
  val1 <- getValFromExpr retFromExpr1
  case val1 of
    ELitBool_T _ (ELitFalse_T _) -> return (Ret (ELitBool_T pos (ELitFalse_T pos)))
    ELitBool_T _ (ELitTrue_T _) -> do
      retFromExpr2 <- evalExpr expr2
      val2 <- getValFromExpr retFromExpr2
      case val2 of
        ELitBool_T _ (ELitTrue_T _) -> return (Ret (ELitBool_T pos (ELitTrue_T pos)))
        ELitBool_T _ (ELitFalse_T _) -> return (Ret (ELitBool_T pos (ELitFalse_T pos)))
        _ -> makeError "Wrong operation argument" pos
    _ -> makeError "Wrong operation argument" pos
evalExpr (ERel_T pos expr1 relOp expr2) = do
  retFromExpr1 <- evalExpr expr1
  val1 <- getValFromExpr retFromExpr1
  retFromExpr2 <- evalExpr expr2
  val2 <- getValFromExpr retFromExpr2
  case (val1, val2) of
    (ELitInt_T _ val1', ELitInt_T _ val2') -> do
      case relOp of
        LTH_T _ -> return (Ret (ELitBool_T pos (if val1' < val2' then ELitTrue_T pos else ELitFalse_T pos)))
        LE_T _ -> return (Ret (ELitBool_T pos (if val1' <= val2' then ELitTrue_T pos else ELitFalse_T pos)))
        GTH_T _ -> return (Ret (ELitBool_T pos (if val1' > val2' then ELitTrue_T pos else ELitFalse_T pos)))
        GE_T _ -> return (Ret (ELitBool_T pos (if val1' >= val2' then ELitTrue_T pos else ELitFalse_T pos)))
        EQU_T _ -> return (Ret (ELitBool_T pos (if val1' == val2' then ELitTrue_T pos else ELitFalse_T pos)))
        NE_T _ -> return (Ret (ELitBool_T pos (if val1' /= val2' then ELitTrue_T pos else ELitFalse_T pos)))
    (EChar_T _ val1', EChar_T _ val2') -> do
      case relOp of
        EQU_T _ -> return (Ret (ELitBool_T pos (if val1' == val2' then ELitTrue_T pos else ELitFalse_T pos)))
        NE_T _ -> return (Ret (ELitBool_T pos (if val1' /= val2' then ELitTrue_T pos else ELitFalse_T pos)))
        _ -> makeError "Wrong operation argument" pos
    (EString_T _ val1', EString_T _ val2') -> do
      case relOp of
        EQU_T _ -> return (Ret (ELitBool_T pos (if val1' == val2' then ELitTrue_T pos else ELitFalse_T pos)))
        NE_T _ -> return (Ret (ELitBool_T pos (if val1' /= val2' then ELitTrue_T pos else ELitFalse_T pos)))
        _ -> makeError "Wrong operation argument" pos
    (ELitBool_T _ val1', ELitBool_T _ val2') -> do
      case relOp of
        EQU_T _ -> return (Ret (ELitBool_T pos (if val1' == val2' then ELitTrue_T pos else ELitFalse_T pos)))
        NE_T _ -> return (Ret (ELitBool_T pos (if val1' /= val2' then ELitTrue_T pos else ELitFalse_T pos)))
        _ -> makeError "Wrong operation argument" pos
    _ -> makeError "Wrong operation argument" pos

evalExpr (ECast_T pos type_ expr) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case (val, type_) of
    (ELitInt_T _ val', Int_T _) -> return (Ret val)
    (ELitInt_T _ val', CharT_T _) -> do
      if val' < 0 || val' > 1114111
        then makeError "Integer too big to convert" pos
        else return (Ret (EChar_T pos (chr (fromInteger val'))))
    (ELitInt_T _ val', Str_T _) -> return (Ret (EString_T pos (show val')))
    (ELitInt_T _ val', Bool_T _) ->
      return (Ret (ELitBool_T pos (if val' == 0 then ELitFalse_T pos else ELitTrue_T pos)))
    (EChar_T _ val', Int_T _) -> return (Ret (ELitInt_T pos (toInteger (ord val'))))
    (EChar_T _ val', CharT_T _) -> return (Ret val)
    (EChar_T _ val', Str_T _) -> return (Ret (EString_T pos [val']))
    (ELitBool_T _ val', Int_T _) -> do
      case val' of
        ELitTrue_T _ -> return (Ret (ELitInt_T pos 1))
        ELitFalse_T _ -> return (Ret (ELitInt_T pos 0))
    (ELitBool_T _ val', Str_T _) -> do
      case val' of
        ELitTrue_T _ -> return (Ret (EString_T pos "True"))
        ELitFalse_T _ -> return (Ret (EString_T pos "False"))
    (ELitBool_T _ val', Bool_T _) -> return (Ret val)
    (EString_T _ val', Str_T _) -> return (Ret val)
    _wrong_type -> makeError "Wrong cast argument" pos

evalExpr (App_T pos ident args) = do
  ret <- evalApp pos ident args
  case ret of
    Ret val -> return (Ret val)
    NoRet -> return NoRet
    Yield _ -> makeError "Unexpected yield" pos
    _ -> undefined -- intended

evalExpr (EGenNext_T pos ident) = do
  ret <- evalGenNext pos ident
  case ret of
    Yield val -> return (Ret val)
    NoRet -> makeError "Unexpected end of generator" pos
    Ret _ -> makeError "Unexpected return" pos
    _ -> undefined -- intended

evalExpr (EListElem_T pos ident expr) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case val of
    ELitInt_T pos val' -> do
      ((envVar, envIter, envList), envProc, envGen) <- ask
      (stVar, stIter, stList) <- get
      case M.lookup ident envList of
        Nothing -> makeError "List not in scope" pos
        Just loc -> do
          case M.lookup loc stList of
            Nothing -> makeError "List not in scope" pos
            Just (type_, list) -> do
              ret <- getFromList pos list (fromInteger val')
              return (Ret ret)
    _ -> makeError "Wrong operation argument" pos

evalExpr (EListLen_T pos ident) = do
  ((envVar, envIter, envList), envProc, envGen) <- ask
  (stVar, stIter, stList) <- get
  case M.lookup ident envList of
    Nothing -> makeError "List not in scope" pos
    Just loc -> do
      case M.lookup loc stList of
        Nothing -> makeError "List not in scope" pos
        Just (type_, list) -> do
          return (Ret (ELitInt_T pos (toInteger (listLen list))))

listLen :: [ELit] -> Integer
listLen = foldr (\ x -> (+) 1) 0

getFromList :: BNFC'Position -> [ELit] -> Integer -> RSE ELit
getFromList pos (x : xs) 0 = return x
getFromList pos (x : xs) n = getFromList pos xs (n - 1)
getFromList pos [] _ = makeError "Index out of bounds" pos

initialEnvSt :: EnvSt
initialEnvSt = (M.empty, M.empty, M.empty)

printBlock :: Block
printBlock = Block_T BNFC'NoPosition []

printProcArg :: [Arg]
printProcArg = undefined -- intended

initialEnvProc :: EnvProc
initialEnvProc =
  M.insert
    (Ident "print")
    (FunRetVoid_T BNFC'NoPosition, printProcArg, printBlock, initialEnvSt, True)
    ( M.insert
        (Ident "print_line")
        (FunRetVoid_T BNFC'NoPosition, printProcArg, printBlock, initialEnvSt, True)
        M.empty
    )

initialEnvGen :: EnvGen
initialEnvGen = M.empty

initialEnv :: Env
initialEnv = (initialEnvSt, initialEnvProc, initialEnvGen)

initialStore :: Store
initialStore = (M.empty, M.empty, M.empty)

main :: IO ()
main = do
  args <- getArgs
  p <- case args of
    [] -> getContents >>= getParsedProgram pProgram
    [fs] -> getParsedProgramFromFile pProgram fs
    _more_args -> error "Program takes zero or one argument"

  typeChecker p

  result <- runExceptT $ runStateT (runReaderT (interpretProgram p) initialEnv) initialStore
  case result of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right (_, _) -> return ()
