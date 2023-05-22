{-# LANGUAGE FlexibleContexts #-}

module Main where

import Prelude
import Data.Char ( ord, chr )
import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when )
import System.IO (hPutStrLn, stderr)

import AbsGrammar
import LexGrammar   ( Token, mkPosToken )
import ParGrammar   ( pProgram, myLexer )
import PrintGrammar ( Print, printTree )
import SkelGrammar  ()
import Parse
import Helper
import TypeChecker
import Types

import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity

getNewLoc :: StoreVar -> Loc
getNewLoc stVar =
  case M.keys stVar of
    [] -> 0
    keys -> maximum keys + 1

interpretProgram :: Program -> RSE ()
interpretProgram (Program_T _ topdefs) = do
  env <- evalTopDefs topdefs
  _ <- local (const env) (evalApp BNFC'NoPosition (Ident "main") [])
  return ()

evalTopDefs :: [TopDef] -> RSE Env
evalTopDefs [] = ask
evalTopDefs (topdef : topdefs) = do
  case topdef of
    ProcDef_T pos ret ident args block -> do
      (envVar, envProc) <- ask
      -- check if procedure is already defined
      case M.lookup ident envProc of
        Just _ -> makeError ("Procedure " ++ getIdentString ident ++ " already defined") pos
        Nothing -> do
          -- add procedure to environment
          let envProc' = M.insert ident (ret, args, block, envVar) envProc
          let newEnv = (envVar, envProc')
          local (const newEnv) (evalTopDefs topdefs)
    GlobVar_T pos type_ ident expr -> do
      (envVar, envProc) <- ask
      stVar <- get
      retFromExpr <- evalExpr expr
      val <- getValFromExpr retFromExpr
      -- check types
      if stringTypeOfType type_ == stringTypeOfElit val
        then do
          -- add variable to environment
          let newLoc = getNewLoc stVar
          put (M.insert newLoc (type_, val) stVar)
          let envVar' = M.insert ident newLoc envVar
          let newEnv = (envVar', envProc)
          local (const newEnv) (evalTopDefs topdefs)
        else do
          makeError "Type mismatch" pos

bindArgsToEnv :: BNFC'Position -> [Arg] -> [ELit] -> [Arg] -> [Loc] -> EnvVar -> RSE EnvVar
bindArgsToEnv _ [] [] [] [] envVar = return envVar

bindArgsToEnv pos (arg : args) (val : vals) refs locs envVar = do
  if stringTypeOfArg arg == stringTypeOfElit val then do
    stVar <- get
    let newLoc = getNewLoc stVar
    put (M.insert newLoc (typeOfArg arg, val) stVar)
    let envVar' = M.insert (getArgIdent arg) newLoc envVar
    (_, envProc) <- ask
    let newEnv = (envVar', envProc)
    local (const newEnv) (bindArgsToEnv pos args vals refs locs envVar')
  else do
    makeError "Wrong argument type" pos

bindArgsToEnv pos args vals (ref : refs) (loc : locs) envVar = do
  stVar <- get
  (_, envProc) <- ask
  case M.lookup loc stVar of
    Just (type_, _) -> do
      if stringTypeOfArg ref == stringTypeOfType type_ then do
        let envVar' = M.insert (getArgIdent ref) loc envVar
        let newEnv = (envVar', envProc)
        local (const newEnv) (bindArgsToEnv pos args vals refs locs envVar')
      else do
        makeError "Wrong argument type" pos
    Nothing -> do
      makeError "Variable not in scope" pos

bindArgsToEnv pos _ _ _ _ _ = do
  error "Wrong number of arguments" pos

evalApp :: BNFC'Position -> Ident -> [FunArg] -> RSE BlockReturn
evalApp pos ident args = do
    if getIdentString ident == "print" then printImpl pos args else do
      if getIdentString ident == "print_line" then printLnImpl pos args else do
        (envVar, envProc) <- ask
        (ret, args', block, envVar') <- case M.lookup ident envProc of
          Just (ret, args', block, envVar') -> return (ret, args', block, envVar')
          Nothing ->
            case pos of
              BNFC'NoPosition -> makeError "There is no 'main' procedure!" pos
              _ -> makeError ("Procedure " ++ getIdentString ident ++ " does not exist") pos
        (argVals, argsByVal) <- evalFunArgsAsValues pos args args'
        (argLocs, argsByRef) <- evalFunArgsAsRefs pos args args'
        newEnv <- bindArgsToEnv pos argsByVal argVals argsByRef argLocs envVar'
        will_return <- if stringFunctionType ret == "void" then return False else return True
        returned <- local (const (newEnv, envProc)) (evalBlock will_return block)
        case returned of
          Ret val -> do
            if stringTypeOfElit val == stringFunctionType ret then return (Ret val) else makeError "Wrong return type" pos
          NoRet -> do
            if stringFunctionType ret == "void" then return NoRet else makeError "Missing return statement" pos


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

evalBlock :: Bool -> Block -> RSE BlockReturn
evalBlock will_return (Block_T pos stmts) = do
  evalStmts will_return pos stmts

evalStmts :: Bool -> BNFC'Position -> [Stmt] -> RSE BlockReturn
evalStmts False _ [] = return NoRet
evalStmts True pos [] = makeError "Missing return statement" pos
evalStmts will_return pos (stmt : stmts) = do
  case stmt of
    Decl_T pos_decl typ ident expr -> do
      retFromExpr <- evalExpr expr
      evaluatedExpr <- getValFromExpr retFromExpr
      if stringTypeOfType typ == stringTypeOfElit evaluatedExpr
        then do
          (envVar, envProc) <- ask
          stVar <- get

          -- add variable to environment
          let newLoc = getNewLoc stVar
          put (M.insert newLoc (typ, evaluatedExpr) stVar)
          let envVar' = M.insert ident newLoc envVar
          let newEnv = (envVar', envProc)
          local (const newEnv) (evalStmts will_return pos stmts)
      else do
        makeError "Type mismatch" pos_decl
    _notDecl -> do
      ret <- evalStmt will_return stmt
      case ret of
        Ret val -> return (Ret val)
        NoRet -> evalStmts will_return pos stmts


evalStmt :: Bool -> Stmt -> RSE BlockReturn
evalStmt _ (Empty_T _) = return NoRet

evalStmt will_return (BStmt_T _ block) = do
  evalBlock will_return block

evalStmt _ Decl_T {} = undefined

evalStmt _ (Decr_T pos ident) = do
  modifyVariable pos ident (\x -> x - 1)
  return NoRet

evalStmt _ (Incr_T pos ident) = do
  modifyVariable pos ident (+ 1)
  return NoRet

evalStmt will_return (Cond_T pos expr block) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> evalBlock will_return block
    ELitBool_T _ (ELitFalse_T _) -> return NoRet
    _CondType -> makeError "Wrong condition type" pos

evalStmt will_return (CondElse_T pos expr block1 block2) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> evalBlock will_return block1
    ELitBool_T _ (ELitFalse_T _) -> evalBlock will_return block2
    _CondType -> makeError "Wrong condition type" pos

evalStmt will_return (While_T pos expr block) = do
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> do
      evalBlock will_return block
      evalStmt will_return (While_T pos expr block)
    ELitBool_T _ (ELitFalse_T _) -> return NoRet
    _CondType -> makeError "Wrong condition type" pos

evalStmt _ (Ass_T pos ident expr) = do
  (envVar, envProc) <- ask
  stVar <- get
  retFromExpr <- evalExpr expr
  val <- getValFromExpr retFromExpr
  case M.lookup ident envVar of
    Nothing -> makeError "Variable not in scope" pos
    Just loc -> do
      case M.lookup loc stVar of
        Just (typ, _) ->
          if stringTypeOfType typ == stringTypeOfElit val
            then put (M.insert loc (typ, val) stVar)
            else makeError "Type mismatch" pos
        Nothing -> makeError "Variable not in scope" pos
  return NoRet

evalStmt will_return (Return_T pos expr) = do
  if will_return then do
    retFromExpr <- evalExpr expr
    val <- getValFromExpr retFromExpr
    return (Ret val)
  else do
    makeError "Unexpected return" pos

evalStmt _ (SExp_T _ expr) = do
  evalExpr expr
  return NoRet

modifyVariable :: BNFC'Position -> Ident -> (Integer -> Integer) -> RSE ()
modifyVariable pos ident modifyFn = do
  stVar <- get
  (envVar, envProc) <- ask
  case M.lookup ident envVar of
    Nothing -> makeError ("Variable " ++ getIdentString ident ++ " not in scope") pos
    Just loc -> do
      case M.lookup loc stVar of
        Nothing -> makeError ("Variable " ++ getIdentString ident ++ " not in scope") pos
        Just (type_, val) -> do
          case val of
            ELitInt_T pos val' -> do
              put (M.insert loc (type_, ELitInt_T pos (modifyFn val')) stVar)
            _ -> makeError ("Variable " ++ getIdentString ident ++ " is not an integer") pos

evalVar :: Var -> RSE Loc
evalVar (Var_T pos ident) = do
  (envVar, envProc) <- ask
  case M.lookup ident envVar of
    Nothing -> makeError ("Variable " ++ getIdentString ident ++ " not in scope") pos
    Just loc -> return loc

getValFromExpr :: BlockReturn -> RSE ELit
getValFromExpr (Ret val) = do
  return val
getValFromExpr NoRet = makeError "No return value" BNFC'NoPosition

evalExpr :: Expr -> RSE BlockReturn
evalExpr (EVar_T pos var) = do
  loc <- evalVar var
  stVar <- get
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
        else
          return (Ret (EChar_T pos (chr (fromInteger val'))))
    (ELitInt_T _ val', Str_T _) -> return (Ret (EString_T pos (show val')))
    (ELitInt_T _ val', Bool_T _) -> return (Ret (ELitBool_T pos (if val' == 0 then ELitFalse_T pos else ELitTrue_T pos)))
    (EChar_T _ val', Int_T _) -> return (Ret (ELitInt_T pos (toInteger (ord val'))))
    (EChar_T _ val', CharT_T _) -> return (Ret val)
    (EChar_T _ val', Str_T _) -> return (Ret (EString_T pos [val']))
    (ELitBool_T _ val', Int_T _) -> do
      case val' of
        ELitTrue_T _ -> return (Ret (ELitInt_T pos 1))
        ELitFalse_T _ -> return (Ret (ELitInt_T pos 0))
    (ELitBool_T _ val', Str_T _) -> return (Ret (EString_T pos (if val' == ELitFalse_T pos then "False" else "True")))
    (ELitBool_T _ val', Bool_T _) -> return (Ret val)
    (EString_T _ val', Str_T _) -> return (Ret val)
    _wrong_type -> makeError "Wrong cast argument" pos

evalExpr (App_T pos ident args) = do
  ret <- evalApp pos ident args
  case ret of
    Ret val -> return (Ret val)
    NoRet -> return NoRet

initialEnvVar :: EnvVar
initialEnvVar = M.empty

printBlock :: Block
printBlock = Block_T BNFC'NoPosition []

printProcArg :: [Arg]
printProcArg = undefined

initialEnvProc :: EnvProc
initialEnvProc =
  M.insert (Ident "print") (FunRetVoid_T BNFC'NoPosition, printProcArg, printBlock, initialEnvVar)
  (M.insert (Ident "print_line") (FunRetVoid_T BNFC'NoPosition, printProcArg, printBlock, initialEnvVar)
  M.empty)

initialEnv :: Env
initialEnv = (initialEnvVar, initialEnvProc)

initialStore :: StoreVar
initialStore = M.empty

main :: IO ()
main = do
  args <- getArgs
  p <- case args of
    []         -> getContents >>= getParsedProgram pProgram
    [fs]       -> getParsedProgramFromFile pProgram fs
    _more_args -> error "Program takes zero or one argument"

  result <- runExceptT $ runStateT (runReaderT (interpretProgram p) initialEnv) initialStore
  case result of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right (_, _) -> return ()
