module TypeChecker where

import AbsGrammar
import LexGrammar   ( Token, mkPosToken )
import ParGrammar   ( pProgram, myLexer )
import PrintGrammar ( Print, printTree )
import SkelGrammar
import Types
import Helper

import Prelude
import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

data TypeT = IntT | CharT | StrT | BoolT | VoidT

type EnvVarT = M.Map Ident Loc

type StoreVarT = M.Map Loc TypeT

type EnvIterT = M.Map Ident Loc

type EnvVarIterT = (EnvVarT, EnvIterT)

type EnvT = EnvVarIterT

type RSET a = ReaderT EnvT (StateT StoreVarT (ExceptT String IO)) a

initEnv :: EnvT
initEnv = (M.empty, M.empty)

initStore :: StoreVarT
initStore = M.empty

typeChecker :: Program -> IO ()
typeChecker program = do
    -- liftIO $ putStrLn "Type checking..."
    rse <- runExceptT (runStateT (runReaderT (checkProgram program) initEnv) initStore)
    return ()

checkProgram :: Program -> RSET ()
checkProgram (Program_T pos topdefs) = do
    -- liftIO $ putStrLn "Checking program"
    checkTopDefs topdefs

checkTopDefs :: [TopDef] -> RSET ()
checkTopDefs [] = return ()

checkTopDefs (topdef : topdefs) = do
    -- liftIO $ putStrLn "Checking topdefs"
    case topdef of
        ProcDef_T pos retval ident args block -> do
            -- checkProcDef retval ident args block
            checkTopDefs topdefs

        GlobVar_T pos type_ ident expr -> do
            env <- checkGlobVar pos type_ ident expr
            local (const env) (checkTopDefs topdefs)

        Gener_T pos type_ ident args block -> do
            -- checkGener type_ ident args block
            checkTopDefs topdefs

checkGlobVar :: BNFC'Position -> Type -> Ident -> Expr -> RSET EnvT
checkGlobVar pos type_ ident expr = do
    -- liftIO $ putStrLn "Checking global var"
    (envVar, envIter) <- ask
    storeVar <- get
    typeExpr <- checkExpr expr
    let typeExpr' = getValType typeExpr
    if stringTypeOfType type_ == stringTypeOfType typeExpr'
        then do
            let loc = M.size storeVar
            let envVar' = M.insert ident loc envVar
            put (M.insert loc (toTypeT type_) storeVar)
            return (envVar', envIter)
        else makeTypeError 
            ("Variable " ++ 
            getIdentString ident ++ 
            " has type " ++ 
            stringTypeOfType typeExpr' ++ 
            " but should have type " ++ 
            stringTypeOfType type_) 
            pos

toTypeT :: Type -> TypeT
toTypeT type_ = case type_ of
    Int_T _ -> IntT
    CharT_T _ -> CharT
    Str_T _ -> StrT
    Bool_T _ -> BoolT

getValType :: TypeT -> Type
getValType type_ = case type_ of
    IntT -> Int_T Nothing
    CharT -> CharT_T Nothing
    StrT -> Str_T Nothing
    BoolT -> Bool_T Nothing
    VoidT -> undefined -- intended

getVarIdent :: Var -> Ident
getVarIdent (Var_T pos ident) = ident

checkExpr :: Expr -> RSET TypeT
checkExpr (EVar_T pos var) = do
    -- liftIO $ putStrLn "Checking expression var"
    (envVar, envIter) <- ask
    storeVar <- get
    let ident = getVarIdent var
    case M.lookup ident envVar of
        Just loc -> do
            let type_ = M.lookup loc storeVar
            case type_ of
                Just type_ -> return type_
                Nothing -> makeTypeError ("Variable " ++ getIdentString ident ++ " not initialized") pos
        Nothing -> makeTypeError ("Variable " ++ getIdentString ident ++ " not declared") pos

checkExpr (ELit_T pos lit) = do
    -- liftIO $ putStrLn "Checking expression literal"
    case lit of
        ELitInt_T _ _ -> return IntT
        EChar_T _ _ -> return CharT
        EString_T _ _ -> return StrT
        ELitBool_T _ _ -> return BoolT

checkExpr (Neg_T pos expr) = do
    -- liftIO $ putStrLn "Checking expression neg"
    typeExpr <- checkExpr expr
    let typeExpr' = getValType typeExpr
    if  stringTypeOfType typeExpr' == "int"
        then return IntT
        else makeTypeError ("Expression " ++ printTree expr ++ " should be of type int") pos

checkExpr (Not_T pos expr) = do
    -- liftIO $ putStrLn "Checking expression not"
    typeExpr <- checkExpr expr
    let typeExpr' = getValType typeExpr
    if  stringTypeOfType typeExpr' == "bool"
        then return BoolT
        else makeTypeError ("Expression " ++ printTree expr ++ " should be of type bool") pos

checkExpr (EMul_T pos expr1 mulop expr2) = do
    -- liftIO $ putStrLn "Checking expression mul"
    typeExpr1 <- checkExpr expr1
    typeExpr2 <- checkExpr expr2
    let typeExpr1' = getValType typeExpr1
    if  stringTypeOfType typeExpr1' == "int"
        then do 
            let typeExpr2' = getValType typeExpr2
            if  stringTypeOfType typeExpr2' == "int"
                then return IntT
                else makeTypeError ("Expression " ++ printTree expr2 ++ " should be of type int") pos
        else makeTypeError ("Expression " ++ printTree expr1 ++ " and " ++ printTree expr2 ++ " should be of type int") pos

checkExpr (EAdd_T pos expr1 addop expr2) = do
    -- liftIO $ putStrLn "Checking expression add"
    typeExpr1 <- checkExpr expr1
    let typeExpr1' = getValType typeExpr1
    if  stringTypeOfType typeExpr1' == "int"
        then do 
            typeExpr2 <- checkExpr expr2
            let typeExpr2' = getValType typeExpr2
            if  stringTypeOfType typeExpr2' == "int"
                then return IntT
                else makeTypeError ("Expression " ++ printTree expr2 ++ " should be of type int") pos
        else makeTypeError ("Expression " ++ printTree expr1 ++ " and " ++ printTree expr2 ++ " should be of type int") pos

checkExpr (ERel_T pos expr1 relop expr2) = do
    -- liftIO $ putStrLn "Checking expression rel"
    typeExpr1 <- checkExpr expr1
    let typeExpr1' = getValType typeExpr1
    if  stringTypeOfType typeExpr1' == "int"
        then do 
            typeExpr2 <- checkExpr expr2
            let typeExpr2' = getValType typeExpr2
            if  stringTypeOfType typeExpr2' == "int"
                then return BoolT
                else makeTypeError ("Expression " ++ printTree expr2 ++ " should be of type int") pos
        else makeTypeError ("Expression " ++ printTree expr1 ++ " and " ++ printTree expr2 ++ " should be of type int") pos

checkExpr (EAnd_T pos expr1 expr2) = do
    -- liftIO $ putStrLn "Checking expression and"
    typeExpr1 <- checkExpr expr1
    let typeExpr1' = getValType typeExpr1
    if  stringTypeOfType typeExpr1' == "bool"
        then do 
            typeExpr2 <- checkExpr expr2
            let typeExpr2' = getValType typeExpr2
            if  stringTypeOfType typeExpr2' == "bool"
                then return BoolT
                else makeTypeError ("Expression " ++ printTree expr2 ++ " should be of type bool") pos
        else makeTypeError ("Expression " ++ printTree expr1 ++ " and " ++ printTree expr2 ++ " should be of type bool") pos

checkExpr (EOr_T pos expr1 expr2) = do
    -- liftIO $ putStrLn "Checking expression or"
    typeExpr1 <- checkExpr expr1
    let typeExpr1' = getValType typeExpr1
    if  stringTypeOfType typeExpr1' == "bool"
        then do 
            typeExpr2 <- checkExpr expr2
            let typeExpr2' = getValType typeExpr2
            if  stringTypeOfType typeExpr2' == "bool"
                then return BoolT
                else makeTypeError ("Expression " ++ printTree expr2 ++ " should be of type bool") pos
        else makeTypeError ("Expression " ++ printTree expr1 ++ " and " ++ printTree expr2 ++ " should be of type bool") pos

checkExpr (ECast_T pos type_ expr) = do
    -- liftIO $ putStrLn "Checking expression cast"
    typeExpr <- checkExpr expr
    let typeExpr' = getValType typeExpr
    case (stringTypeOfType typeExpr', type_) of
        ("int", Int_T _) -> return IntT
        ("int", CharT_T _) -> return CharT
        ("int", Str_T _) -> return StrT
        ("int", Bool_T _) -> return BoolT
        ("char", Int_T _) -> return IntT
        ("char", CharT_T _) -> return CharT
        ("char", Str_T _) -> return StrT
        ("str", Str_T _) -> return StrT
        ("bool", Int_T _) -> return IntT
        ("bool", Str_T _) -> return StrT
        ("bool", Bool_T _) -> return BoolT
        _ -> makeTypeError ("Cannot cast " ++ stringTypeOfType typeExpr' ++ " to " ++ stringTypeOfType type_) pos

checkExpr (App_T pos ident funargs) = do 
    -- liftIO $ putStrLn "Checking expression app not implemented yet"
    return VoidT

checkExpr (EGenNext_T pos ident) = do 
    -- liftIO $ putStrLn "Checking expression genNext not implemented yet"
    return VoidT

