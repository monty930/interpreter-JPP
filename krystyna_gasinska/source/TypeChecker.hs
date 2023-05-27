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

type StoreIterT = M.Map Loc TypeT

type EnvIterT = M.Map Ident Loc

type EnvProcT = M.Map Ident (TypeT, [TypeT])

type EnvGenT = M.Map Ident (TypeT, [TypeT])

type EnvVarIterT = (EnvVarT, EnvIterT)

type EnvT = (EnvVarIterT, EnvProcT, EnvGenT)

type RSET a = ReaderT EnvT (StateT StoreVarT (ExceptT String IO)) a

initEnv :: EnvT
initEnv = ((M.empty, M.empty), M.empty, M.empty)

initStore :: StoreVarT
initStore = M.empty

typeChecker :: Program -> IO ()
typeChecker program = do
    rse <- runExceptT (runStateT (runReaderT (checkProgram program) initEnv) initStore)
    return ()

checkProgram :: Program -> RSET ()
checkProgram (Program_T pos topdefs) = do
    checkTopDefs topdefs

checkTopDefs :: [TopDef] -> RSET ()
checkTopDefs [] = return ()

checkTopDefs (topdef : topdefs) = do
    case topdef of
        ProcDef_T pos retval ident args block -> do
            ((envVar, envIter), envProc, envGen) <- ask
            envP <- checkProcDef pos retval ident args block
            local (const ((envVar, envIter), envP, envGen)) (checkTopDefs topdefs)

        GlobVar_T pos type_ ident expr -> do
            env <- checkGlobVar pos type_ ident expr
            local (const env) (checkTopDefs topdefs)

        Gener_T pos type_ ident args block -> do
            ((envVar, envIter), envProc, envGen) <- ask
            envG <- checkGener pos type_ ident args block
            local (const ((envVar, envIter), envProc, envG)) (checkTopDefs topdefs)

checkGener :: BNFC'Position -> Type -> Ident -> [Arg] -> Block -> RSET EnvGenT
checkGener pos type_ ident args block = do
    ((envVar, envIter), envProc, envGen) <- ask
    (envVar', argTypes) <- insertArgsToEnvProc pos (envVar, []) args
    let type_' = toTypeT type_
    let envGen' = M.insert ident (type_', argTypes) envGen
    let ret_type = typeTToBlockRetType type_'
    local (const ((envVar', envIter), envProc, envGen')) (checkBlock ret_type block)
    return envGen'

retValToTypeT :: RetVal -> TypeT
retValToTypeT retval = case retval of
    FunRetVoid_T _ -> VoidT
    FunRetVal_T _ type_ -> toTypeT type_

checkProcDef :: BNFC'Position -> RetVal -> Ident -> [Arg] -> Block -> RSET EnvProcT
checkProcDef pos retval ident args block = do
    ((envVar, envIter), envProc, envGen) <- ask
    (envVar', argTypes) <- insertArgsToEnvProc pos (envVar, []) args
    let type_ = retValToTypeT retval
    let envProc' = M.insert ident (type_, argTypes) envProc
    let ret_type = typeTToBlockRetType type_
    local (const ((envVar', envIter), envProc', envGen)) (checkBlock ret_type block)
    return envProc'

typeTToBlockRetType :: TypeT -> BlockRetType
typeTToBlockRetType type_ = 
    case type_ of
        VoidT -> NoRetType
        type_' -> RetType (getValType type_)

insertArgsToEnvProc :: BNFC'Position -> (EnvVarT, [TypeT]) -> [Arg] -> RSET (EnvVarT, [TypeT])
insertArgsToEnvProc pos envVar [] = return envVar

insertArgsToEnvProc pos (envVar, argTypes) (arg : args) = do
    storeVar <- get
    let type_ = toTypeT (typeOfArg arg)
    let ident = getArgIdent arg
    let loc = getNewLocT storeVar
    let envVar' = M.insert ident loc envVar
    put (M.insert loc type_ storeVar)
    insertArgsToEnvProc pos (envVar', argTypes ++ [type_]) args

checkBlock :: BlockRetType -> Block -> RSET ()
checkBlock ret_type (Block_T pos stmts) = do
    checkStmts ret_type stmts

checkStmts :: BlockRetType -> [Stmt] -> RSET ()
checkStmts ret_type [] = return ()

checkStmts ret_type (stmt : stmts) = do
    case stmt of 
        Decl_T pos type_ ident expr -> do 
            env <- checkDecl pos type_ ident expr
            local (const env) (checkStmts ret_type stmts)
        _no_decl -> do
            checkStmt ret_type stmt
            checkStmts ret_type stmts

getNewLocT :: StoreVarT -> Loc
getNewLocT stVar =
  case M.keys stVar of
    [] -> 0
    keys -> maximum keys + 1

checkDecl :: BNFC'Position -> Type -> Ident -> Expr -> RSET EnvT
checkDecl pos type_ ident expr = do
    ((envVar, envIter), envProc, envGen) <- ask
    storeVar <- get
    typeExpr <- checkExpr expr
    let typeExpr' = getValType typeExpr
    if stringTypeOfType type_ == stringTypeOfType typeExpr'
        then do
            let loc = getNewLocT storeVar
            let envVar' = M.insert ident loc envVar
            put (M.insert loc (toTypeT type_) storeVar)
            return ((envVar', envIter), envProc, envGen)
        else makeTypeError 
            ("Variable " ++ 
            getIdentString ident ++ 
            " has type " ++ 
            stringTypeOfType typeExpr' ++ 
            " but should have type " ++ 
            stringTypeOfType type_) 
            pos

checkStmt :: BlockRetType -> Stmt -> RSET ()
checkStmt ret_type (Empty_T pos) = return ()

checkStmt ret_type (BStmt_T pos block) = do
    checkBlock ret_type block

checkStmt ret_type (Decl_T pos type_ ident expr) = undefined -- intended

checkStmt ret_type (Ass_T pos ident expr) = do 
    ((envVar, envIter), envProc, envGen) <- ask
    storeVar <- get
    typeExpr <- checkExpr expr
    let typeExpr' = getValType typeExpr
    case M.lookup ident envVar of 
        Nothing -> do 
            makeTypeError ("Variable " ++ show ident ++ " undefined") pos
        Just loc -> case M.lookup loc storeVar of 
            Nothing -> do 
                makeTypeError ("Variable " ++ show ident ++ " undefined") pos
            Just type_ -> do
                let type_' = getValType type_
                if stringTypeOfType type_' == stringTypeOfType typeExpr'
                    then return ()
                    else makeTypeError 
                        ("Variable " ++ 
                        getIdentString ident ++ 
                        " has type " ++ 
                        stringTypeOfType typeExpr' ++ 
                        " but should have type " ++ 
                        stringTypeOfType type_') 
                        pos

checkStmt ret_type (SExp_T pos expr) = do
    checkExpr expr
    return ()

checkStmt ret_type (Cond_T pos expr block) = do 
    type_ <- checkExpr expr
    let type_' = getValType type_
    if stringTypeOfType type_' == "bool"
        then checkBlock ret_type block
        else makeTypeError 
            ("Condition has type " ++ 
            stringTypeOfType type_' ++ 
            " but should have type bool") 
            pos

checkStmt ret_type (CondElse_T pos expr block1 block2) = do 
    type_ <- checkExpr expr
    let type_' = getValType type_
    if stringTypeOfType type_' == "bool"
        then do
            checkBlock ret_type block1
            checkBlock ret_type block2
        else makeTypeError 
            ("Condition has type " ++ 
            stringTypeOfType type_' ++ 
            " but should have type bool") 
            pos

checkStmt ret_type (While_T pos expr block) = do
    type_ <- checkExpr expr
    let type_' = getValType type_
    if stringTypeOfType type_' == "bool"
        then checkBlock ret_type block
        else makeTypeError 
            ("Condition has type " ++ 
            stringTypeOfType type_' ++ 
            " but should have type bool") 
            pos

checkStmt ret_type (ForGen_T pos ident1 ident2 funargs block) = do
    liftIO $ putStrLn "STMT FOR UNDEFINED"
    return ()

checkStmt retType (Incr_T pos ident) = 
    checkIncrDecr pos ident

checkStmt retType (Decr_T pos ident) = do
    checkIncrDecr pos ident

checkStmt retType (Return_T pos expr) = do
    if retType == NoRetType
        then makeTypeError "Return in void function" pos
        else do
    type_ <- checkExpr expr
    let type_' = getValType type_
    retTypeT <- blockRetToTypeReturn pos retType
    let retType' = getValType retTypeT
    if stringTypeOfType type_' == stringTypeOfType retType'
        then return ()
        else makeTypeError 
            ("Return has type " ++ 
            stringTypeOfType type_' ++ 
            " but should have type " ++ 
            stringTypeOfType retType') 
            pos

checkStmt retType (Yield_T pos expr) = do 
    type_ <- checkExpr expr
    let type_' = getValType type_
    retTypeT <- blockRetToTypeYield pos retType
    let retType' = getValType retTypeT
    if stringTypeOfType type_' == stringTypeOfType retType'
        then return ()
        else makeTypeError 
            ("Yield has type " ++ 
            stringTypeOfType type_' ++ 
            " but should have type " ++ 
            stringTypeOfType retType') 
            pos

checkStmt retType (DeclGen_T pos type_ ident expr) =
    undefined -- intended

blockRetToTypeReturn :: BNFC'Position -> BlockRetType -> RSET TypeT
blockRetToTypeReturn pos (RetType type_) = return (toTypeT type_)
blockRetToTypeReturn pos NoRetType = return VoidT 
blockRetToTypeReturn pos _ = makeTypeError "Yield outside generator" pos

blockRetToTypeYield :: BNFC'Position -> BlockRetType -> RSET TypeT
blockRetToTypeYield pos (YieldType type_) = return (toTypeT type_)
blockRetToTypeYield pos NoRetType = return VoidT
blockRetToTypeYield pos _ = makeTypeError "Return in generator" pos

checkIncrDecr :: BNFC'Position -> Ident -> RSET ()
checkIncrDecr pos ident = do
    ((envVar, _envIter), _envProc, _envGen) <- ask
    storeVar <- get
    case M.lookup ident envVar of 
        Nothing -> do 
            makeTypeError ("Variable " ++ show ident ++ " undefined") pos
        Just loc -> case M.lookup loc storeVar of 
            Nothing -> do 
                makeTypeError ("Variable " ++ show ident ++ " undefined") pos
            Just type_ -> do
                let type_' = getValType type_
                if stringTypeOfType type_' == "int"
                    then return ()
                    else makeTypeError 
                        ("Variable " ++ 
                        getIdentString ident ++ 
                        " has type " ++ 
                        stringTypeOfType type_' ++ 
                        " but should have type int") 
                        pos

checkGlobVar :: BNFC'Position -> Type -> Ident -> Expr -> RSET EnvT
checkGlobVar pos type_ ident expr = do
    ((envVar, envIter), envProc, envGen) <- ask
    storeVar <- get
    typeExpr <- checkExpr expr
    let typeExpr' = getValType typeExpr
    if stringTypeOfType type_ == stringTypeOfType typeExpr'
        then do
            let loc = getNewLocT storeVar
            let envVar' = M.insert ident loc envVar
            put (M.insert loc (toTypeT type_) storeVar)
            return ((envVar', envIter), envProc, envGen)
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

checkExpr :: Expr -> RSET TypeT
checkExpr (EVar_T pos var) = do
    ((envVar, _envIter), _envProc, _envGen) <- ask
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
    case lit of
        ELitInt_T _ _ -> return IntT
        EChar_T _ _ -> return CharT
        EString_T _ _ -> return StrT
        ELitBool_T _ _ -> return BoolT

checkExpr (Neg_T pos expr) = do
    typeExpr <- checkExpr expr
    let typeExpr' = getValType typeExpr
    if  stringTypeOfType typeExpr' == "int"
        then return IntT
        else makeTypeError "Expression should be of type int" pos

checkExpr (Not_T pos expr) = do
    typeExpr <- checkExpr expr
    let typeExpr' = getValType typeExpr
    if  stringTypeOfType typeExpr' == "bool"
        then return BoolT
        else makeTypeError "Expression should be of type bool" pos

checkExpr (EMul_T pos expr1 mulop expr2) = do
    typeExpr1 <- checkExpr expr1
    typeExpr2 <- checkExpr expr2
    let typeExpr1' = getValType typeExpr1
    if  stringTypeOfType typeExpr1' == "int"
        then do 
            let typeExpr2' = getValType typeExpr2
            if  stringTypeOfType typeExpr2' == "int"
                then return IntT
                else makeTypeError "Expression should be of type int" pos
        else makeTypeError ("Expression" ++ " should be of type int") pos

checkExpr (EAdd_T pos expr1 addop expr2) = do
    typeExpr1 <- checkExpr expr1
    let typeExpr1' = getValType typeExpr1
    typeExpr2 <- checkExpr expr2
    let typeExpr2' = getValType typeExpr2
    let typeStr1 = stringTypeOfType typeExpr1'
    let typeStr2 = stringTypeOfType typeExpr2'
    case (typeStr1, typeStr2) of 
        ("int", "int") -> return IntT
        ("string", "string") -> return StrT
        _ -> makeTypeError "Add expression should be of type int or string" pos

checkExpr (ERel_T pos expr1 relop expr2) = do
    typeExpr1 <- checkExpr expr1
    let typeExpr1' = getValType typeExpr1
    if  stringTypeOfType typeExpr1' == "int"
        then do 
            typeExpr2 <- checkExpr expr2
            let typeExpr2' = getValType typeExpr2
            if  stringTypeOfType typeExpr2' == "int"
                then return BoolT
                else makeTypeError "Expression should be of type int" pos
        else 
            if  stringTypeOfType typeExpr1' == "string" then
                case relop of 
                    EQU_T _ -> do
                        typeExpr2 <- checkExpr expr2
                        let typeExpr2' = getValType typeExpr2
                        if  stringTypeOfType typeExpr2' == "string"
                            then return BoolT
                            else makeTypeError "Expression should be of type string" pos
                    NE_T _ -> do
                        typeExpr2 <- checkExpr expr2
                        let typeExpr2' = getValType typeExpr2
                        if  stringTypeOfType typeExpr2' == "string"
                            then return BoolT
                            else makeTypeError "Expression should be of type string" pos
                    _ -> makeTypeError "Wrong expression type" pos
            else 
                makeTypeError "Wrong expression type" pos

checkExpr (EAnd_T pos expr1 expr2) = do
    typeExpr1 <- checkExpr expr1
    let typeExpr1' = getValType typeExpr1
    if  stringTypeOfType typeExpr1' == "bool"
        then do 
            typeExpr2 <- checkExpr expr2
            let typeExpr2' = getValType typeExpr2
            if  stringTypeOfType typeExpr2' == "bool"
                then return BoolT
                else makeTypeError "Expression should be of type bool" pos
        else makeTypeError ("Expression" ++ " should be of type bool") pos

checkExpr (EOr_T pos expr1 expr2) = do
    typeExpr1 <- checkExpr expr1
    let typeExpr1' = getValType typeExpr1
    if  stringTypeOfType typeExpr1' == "bool"
        then do 
            typeExpr2 <- checkExpr expr2
            let typeExpr2' = getValType typeExpr2
            if  stringTypeOfType typeExpr2' == "bool"
                then return BoolT
                else makeTypeError "Expression should be of type bool" pos
        else makeTypeError ("Expression" ++ " should be of type bool") pos

checkExpr (ECast_T pos type_ expr) = do
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

checkExpr (EGenNext_T pos ident) = do 
    return VoidT

checkExpr (App_T pos ident funargs) = do 
    ((envVar, envIter), envProc, envGen) <- ask
    storeVar <- get
    case M.lookup ident envProc of
        Nothing -> do 
            if getIdentString ident == "print" || getIdentString ident == "print_line"
                then do
                    checkArgs pos funargs [StrT]
                    return VoidT
                else
                    makeTypeError
                        ("Function " ++
                        getIdentString ident ++
                        " not declared") pos
        Just (type_, argsTypes) -> do
            checkArgs pos funargs argsTypes
            return type_

checkArgs :: BNFC'Position -> [FunArg] -> [TypeT] -> RSET ()
checkArgs pos [] [] = return ()

checkArgs pos (farg : fargs) (argT : argsT) = do 
    case farg of 
        AsValue_T pos expr -> do 
            typeExpr <- checkExpr expr
            let typeExpr' = getValType typeExpr
            let argT' = getValType argT
            if  stringTypeOfType typeExpr' == stringTypeOfType argT'
                then checkArgs pos fargs argsT
                else
                    makeTypeError 
                        ("Argument should be of type " ++
                        stringTypeOfType argT') pos
        AsRef_T pos var -> do 
            let ident = getVarIdent var
            ((envVar, envIter), envProc, envGen) <- ask
            storeVar <- get
            case M.lookup ident envVar of
                Nothing -> makeTypeError (
                    "Variable " ++
                    getIdentString ident ++
                    " not declared") pos
                Just loc -> do 
                    case M.lookup loc storeVar of
                        Nothing -> 
                            makeTypeError
                                ("Variable " ++
                                getIdentString ident ++
                                " not declared") pos
                        Just typeT_ -> do
                            let typeOfArg_ = getValType typeT_
                            let argT' = getValType argT
                            if  stringTypeOfType typeOfArg_ == stringTypeOfType argT'
                                then checkArgs pos fargs argsT
                                else 
                                    makeTypeError 
                                        ("Argument should be of type " ++
                                        stringTypeOfType argT') pos

checkArgs pos _ _ = makeTypeError "Wrong number of arguments" pos



