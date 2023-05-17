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

import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity

type Loc = Int

type EnvVar = M.Map Ident Loc

type StoreVar = M.Map Loc (Type, ELit)

type EnvProc = M.Map Ident (RetVal, [Arg], Block, EnvVar)

type Env = (EnvVar, EnvProc)

type RSE a = ReaderT Env (StateT StoreVar (ExceptT String IO)) a

getNewLoc :: StoreVar -> Loc
getNewLoc stVar =
  case M.keys stVar of
    [] -> 0
    keys -> maximum keys + 1

showBNFC :: BNFC'Position -> String
showBNFC (Just (line, col)) = "line " ++ show line ++ ", column " ++ show col
showBNFC Nothing = ""

makeError message bnfcPos = do
  let errorMessage = showBNFC bnfcPos ++ " " ++ message
  errorWithoutStackTrace errorMessage

interpretProgram :: Program -> RSE ()
interpretProgram (Program_T _ topdefs) = do
  env <- evalTopDefs topdefs
  local (const env) (evalApp BNFC'NoPosition (Ident "main") [])

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
      val <- evalExpr expr
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

evalApp :: BNFC'Position -> Ident -> [FunArg] -> RSE ()
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
        local (const (newEnv, envProc)) (evalBlock will_return block)

evalFunArgsAsValues :: BNFC'Position -> [FunArg] -> [Arg] -> RSE ([ELit], [Arg])
evalFunArgsAsValues pos args idfs = do
  evalFunArgsAsValuesAcc pos args idfs ([], [])

evalFunArgsAsValuesAcc :: BNFC'Position -> [FunArg] -> [Arg] -> ([ELit], [Arg]) -> RSE ([ELit], [Arg])
evalFunArgsAsValuesAcc pos [] [] acc = return acc

evalFunArgsAsValuesAcc pos (arg : args) (idf : idfs) (argVals, argsByVal) = do
  case arg of
    AsValue_T pos expr -> do
      val <- evalExpr expr
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

printImpl :: BNFC'Position -> [FunArg] -> RSE ()
printImpl pos args = do
  case args of
    [arg] -> do
      (AsValue_T pos expr) <- return arg
      val <- evalExpr expr
      case val of
        EString_T pos str -> liftIO $ putStr str
        _ -> makeError "Wrong argument type" pos
    _ -> makeError "Wrong number of arguments" pos

printLnImpl :: BNFC'Position -> [FunArg] -> RSE ()
printLnImpl pos args = do
  case args of
    [arg] -> do
      (AsValue_T pos expr) <- return arg
      val <- evalExpr expr
      case val of
        EString_T pos str -> liftIO $ putStr (str ++ "\n")
        _ -> makeError "Wrong argument type" pos
    _ -> makeError "Wrong number of arguments" pos

evalBlock :: Bool -> Block -> RSE ()
evalBlock will_return (Block_T pos stmts) = do
  evalStmts will_return pos stmts

evalStmts :: Bool -> BNFC'Position -> [Stmt] -> RSE ()
evalStmts False _ [] = return ()
evalStmts True pos [] = makeError "Missing return statement" pos
evalStmts will_return pos (stmt : stmts) = do
  case stmt of
    Decl_T pos_decl typ ident expr -> do
      evaluatedExpr <- evalExpr expr
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
      evalStmt will_return stmt
      evalStmts will_return pos stmts

evalStmt :: Bool -> Stmt -> RSE ()
evalStmt _ (Empty_T _) = return ()

evalStmt will_return (BStmt_T _ block) = do
  evalBlock will_return block

evalStmt _ Decl_T {} = undefined

evalStmt _ (App_T pos ident args) = do
  evalApp pos ident args

evalStmt _ (Decr_T pos ident) = modifyVariable pos ident (\x -> x - 1)

evalStmt _ (Incr_T pos ident) = modifyVariable pos ident (+ 1)

evalStmt will_return (Cond_T pos expr block) = do
  val <- evalExpr expr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> evalBlock will_return block
    ELitBool_T _ (ELitFalse_T _) -> return ()
    _CondType -> makeError "Wrong condition type" pos

evalStmt will_return (CondElse_T pos expr block1 block2) = do
  val <- evalExpr expr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> evalBlock will_return block1
    ELitBool_T _ (ELitFalse_T _) -> evalBlock will_return block2
    _CondType -> makeError "Wrong condition type" pos

evalStmt will_return (While_T pos expr block) = do
  val <- evalExpr expr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> do
      evalBlock will_return block
      evalStmt will_return (While_T pos expr block)
    ELitBool_T _ (ELitFalse_T _) -> return ()
    _CondType -> makeError "Wrong condition type" pos

evalStmt _ (Ass_T pos ident expr) = do
  (envVar, envProc) <- ask
  stVar <- get
  val <- evalExpr expr
  case M.lookup ident envVar of
    Nothing -> makeError "Variable not in scope" pos
    Just loc -> do
      case M.lookup loc stVar of
        Just (typ, _) ->
          if stringTypeOfType typ == stringTypeOfElit val
            then put (M.insert loc (typ, val) stVar)
            else makeError "Type mismatch" pos
        Nothing -> makeError "Variable not in scope" pos
  return ()

evalStmt will_return (Return_T pos expr) = do
  if will_return then do 
    val <- evalExpr expr 
    

evalStmt _ (SExp_T _ expr) = undefined

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

evalExpr :: Expr -> RSE ELit
evalExpr (EVar_T pos var) = do
  loc <- evalVar var
  stVar <- get
  case M.lookup loc stVar of
    Nothing -> makeError "Variable not in scope" pos
    Just (_, val) -> return val

evalExpr (ELit_T _ lit) = return lit

evalExpr (Neg_T pos expr) = do
  val <- evalExpr expr
  case val of
    ELitInt_T _ val -> return (ELitInt_T pos (- val))
    _ -> makeError "Wrong operation argument" pos

evalExpr (Not_T pos expr) = do
  val <- evalExpr expr
  case val of
    ELitBool_T _ (ELitTrue_T _) -> return (ELitBool_T pos (ELitFalse_T pos))
    ELitBool_T _ (ELitFalse_T _) -> return (ELitBool_T pos (ELitTrue_T pos))
    _ -> makeError "Wrong operation argument" pos

evalExpr (EMul_T pos expr1 mulOp expr2) = do
  val1 <- evalExpr expr1
  val2 <- evalExpr expr2
  case (val1, val2) of
    (ELitInt_T _ val1', ELitInt_T _ val2') -> do
      case mulOp of
        Times_T _ -> return (ELitInt_T pos (val1' * val2'))
        Div_T _ -> do
          if val2' == 0
            then makeError "Division by zero" pos
            else return (ELitInt_T pos (val1' `div` val2'))
        Mod_T _ -> return (ELitInt_T pos (val1' `mod` val2'))
    _ -> makeError "Wrong operation argument" pos

evalExpr (EAdd_T pos expr1 addOp expr2) = do
  val1 <- evalExpr expr1
  val2 <- evalExpr expr2
  case (val1, val2) of
    (ELitInt_T _ val1', ELitInt_T _ val2') -> do
      case addOp of
        Plus_T _ -> return (ELitInt_T pos (val1' + val2'))
        Minus_T _ -> return (ELitInt_T pos (val1' - val2'))
    (EString_T _ val1', EString_T _ val2') -> do
      case addOp of
        Plus_T _ -> return (EString_T pos (val1' ++ val2'))
        _ -> makeError "Wrong operation argument" pos
    _ -> makeError "Wrong operation argument" pos

evalExpr (EOr_T pos expr1 expr2) = do
  val1 <- evalExpr expr1
  case val1 of
    ELitBool_T _ (ELitTrue_T _) -> return (ELitBool_T pos (ELitTrue_T pos))
    ELitBool_T _ (ELitFalse_T _) -> do
      val2 <- evalExpr expr2
      case val2 of
        ELitBool_T _ (ELitTrue_T _) -> return (ELitBool_T pos (ELitTrue_T pos))
        ELitBool_T _ (ELitFalse_T _) -> return (ELitBool_T pos (ELitFalse_T pos))
        _ -> makeError "Wrong operation argument" pos
    _ -> makeError "Wrong operation argument" pos

evalExpr (EAnd_T pos expr1 expr2) = do
  val1 <- evalExpr expr1
  case val1 of
    ELitBool_T _ (ELitFalse_T _) -> return (ELitBool_T pos (ELitFalse_T pos))
    ELitBool_T _ (ELitTrue_T _) -> do
      val2 <- evalExpr expr2
      case val2 of
        ELitBool_T _ (ELitTrue_T _) -> return (ELitBool_T pos (ELitTrue_T pos))
        ELitBool_T _ (ELitFalse_T _) -> return (ELitBool_T pos (ELitFalse_T pos))
        _ -> makeError "Wrong operation argument" pos
    _ -> makeError "Wrong operation argument" pos

evalExpr (ERel_T pos expr1 relOp expr2) = do
  val1 <- evalExpr expr1
  val2 <- evalExpr expr2
  case (val1, val2) of
    (ELitInt_T _ val1', ELitInt_T _ val2') -> do
      case relOp of
        LTH_T _ -> return (ELitBool_T pos (if val1' < val2' then ELitTrue_T pos else ELitFalse_T pos))
        LE_T _ -> return (ELitBool_T pos (if val1' <= val2' then ELitTrue_T pos else ELitFalse_T pos))
        GTH_T _ -> return (ELitBool_T pos (if val1' > val2' then ELitTrue_T pos else ELitFalse_T pos))
        GE_T _ -> return (ELitBool_T pos (if val1' >= val2' then ELitTrue_T pos else ELitFalse_T pos))
        EQU_T _ -> return (ELitBool_T pos (if val1' == val2' then ELitTrue_T pos else ELitFalse_T pos))
        NE_T _ -> return (ELitBool_T pos (if val1' /= val2' then ELitTrue_T pos else ELitFalse_T pos))
    (EChar_T _ val1', EChar_T _ val2') -> do
      case relOp of
        EQU_T _ -> return (ELitBool_T pos (if val1' == val2' then ELitTrue_T pos else ELitFalse_T pos))
        NE_T _ -> return (ELitBool_T pos (if val1' /= val2' then ELitTrue_T pos else ELitFalse_T pos))
        _ -> makeError "Wrong operation argument" pos
    (EString_T _ val1', EString_T _ val2') -> do
      case relOp of
        EQU_T _ -> return (ELitBool_T pos (if val1' == val2' then ELitTrue_T pos else ELitFalse_T pos))
        NE_T _ -> return (ELitBool_T pos (if val1' /= val2' then ELitTrue_T pos else ELitFalse_T pos))
        _ -> makeError "Wrong operation argument" pos
    (ELitBool_T _ val1', ELitBool_T _ val2') -> do
      case relOp of
        EQU_T _ -> return (ELitBool_T pos (if val1' == val2' then ELitTrue_T pos else ELitFalse_T pos))
        NE_T _ -> return (ELitBool_T pos (if val1' /= val2' then ELitTrue_T pos else ELitFalse_T pos))
        _ -> makeError "Wrong operation argument" pos
    _ -> makeError "Wrong operation argument" pos


evalExpr (ECast_T pos type_ expr) = do
  val <- evalExpr expr
  case (val, type_) of
    (ELitInt_T _ val', Int_T _) -> return val
    (ELitInt_T _ val', CharT_T _) -> do
      if val' < 0 || val' > 1114111
        then makeError "Integer too big to convert" pos
        else
          return (EChar_T pos (chr (fromInteger val')))
    (ELitInt_T _ val', Str_T _) -> return (EString_T pos (show val'))
    (ELitInt_T _ val', Bool_T _) -> return (ELitBool_T pos (if val' == 0 then ELitFalse_T pos else ELitTrue_T pos))
    (EChar_T _ val', Int_T _) -> return (ELitInt_T pos (toInteger (ord val')))
    (EChar_T _ val', CharT_T _) -> return val
    (EChar_T _ val', Str_T _) -> return (EString_T pos [val'])
    (ELitBool_T _ val', Int_T _) -> do
      case val' of
        ELitTrue_T _ -> return (ELitInt_T pos 1)
        ELitFalse_T _ -> return (ELitInt_T pos 0)
    (ELitBool_T _ val', Str_T _) -> return (EString_T pos (if val' == ELitFalse_T pos then "False" else "True"))
    (ELitBool_T _ val', Bool_T _) -> return val
    (EString_T _ val', Str_T _) -> return val
    _wrong_type -> makeError "Wrong cast argument" pos

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

-- evalStmt (Decr_T pos ident) = do
--   stVar <- get
--   (envVar, envProc) <- ask
--   case M.lookup ident envVar of 
--     Nothing -> makeError ("Variable " ++ getIdentString ident ++ " not in scope") pos
--     Just loc -> do
--       case M.lookup loc stVar of
--         Nothing -> makeError ("Variable " ++ getIdentString ident ++ " not in scope") pos
--         Just (type_, val) -> do
--           case val of
--             ELitInt_T pos val -> do
--               put (M.insert loc (type_, ELitInt_T pos (val - 1)) stVar)
--             _ -> makeError ("Variable " ++ getIdentString ident ++ " is not an integer") pos

-- evalStmt (Incr_T pos ident) = do
--   stVar <- get
--   (envVar, envProc) <- ask
--   case M.lookup ident envVar of 
--     Nothing -> makeError ("Variable " ++ getIdentString ident ++ " not in scope") pos
--     Just loc -> do
--       case M.lookup loc stVar of
--         Nothing -> makeError ("Variable " ++ getIdentString ident ++ " not in scope") pos
--         Just (type_, val) -> do
--           case val of
--             ELitInt_T pos val -> do
--               put (M.insert loc (type_, ELitInt_T pos (val + 1)) stVar)
--             _ -> makeError ("Variable " ++ getIdentString ident ++ " is not an integer") pos
