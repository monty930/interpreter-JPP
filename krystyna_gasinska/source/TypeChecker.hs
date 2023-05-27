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
    deriving (Show, Eq)

type EnvVarT = M.Map Ident Loc

type StoreVarT = M.Map Loc TypeT

type StoreListT = M.Map Loc TypeT

type EnvListT = M.Map Ident Loc

type StoreIterT = M.Map Loc TypeT

type EnvIterT = M.Map Ident Loc

type EnvProcT = M.Map Ident (TypeT, [TypeT], Bool)

type EnvGenT = M.Map Ident (TypeT, [TypeT])

type EnvStT = (EnvVarT, EnvIterT, EnvListT)

type EnvT = (EnvStT, EnvProcT, EnvGenT)

type StoreT = (StoreVarT, StoreIterT, StoreListT)

type RSET a = ReaderT EnvT (StateT StoreT (ExceptT String IO)) a

initEnv :: EnvT
initEnv = ((M.empty, M.empty, M.empty), M.empty, M.empty)

initStore :: StoreT
initStore = (M.empty, M.empty, M.empty)

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
        ProcDecl_T pos retval ident args -> do
            ((envVar, envIter, envList), envProc, envGen) <- ask
            envP <- checkProcDecl pos retval ident args
            local (const ((envVar, envIter, envList), envP, envGen)) (checkTopDefs topdefs)

        ProcDef_T pos retval ident args block -> do
            ((envVar, envIter, envList), envProc, envGen) <- ask
            envP <- checkProcDef pos retval ident args block
            local (const ((envVar, envIter, envList), envP, envGen)) (checkTopDefs topdefs)

        GlobVar_T pos type_ ident expr -> do
            env <- checkGlobVar pos type_ ident expr
            local (const env) (checkTopDefs topdefs)

        Gener_T pos type_ ident args block -> do
            ((envVar, envIter, envList), envProc, envGen) <- ask
            envG <- checkGener pos type_ ident args block
            local (const ((envVar, envIter, envList), envProc, envG)) (checkTopDefs topdefs)

        ListGlobDecl_T pos type_ ident exprs -> do
            ((envVar, envIter, envList), envProc, envGen) <- ask
            envL <- checkListGlobDecl pos type_ ident exprs
            local (const ((envVar, envIter, envL), envProc, envGen)) (checkTopDefs topdefs)

checkListGlobDecl :: BNFC'Position -> Type -> Ident -> [Expr] -> RSET EnvListT
checkListGlobDecl pos type_ ident exprs = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (storeVar, storeIter, stList) <- get
    let type_' = toTypeT type_
    let loc = getNewLocT storeVar
    let envList' = M.insert ident loc envList
    put (storeVar, storeIter, M.insert loc type_' stList)
    checkExprs pos exprs type_
    return envList'

checkGener :: BNFC'Position -> Type -> Ident -> [Arg] -> Block -> RSET EnvGenT
checkGener pos type_ ident args block = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (envVar', argTypes) <- insertArgsToEnvProc pos (envVar, []) args
    let type_' = toTypeT type_
    let envGen' = M.insert ident (type_', argTypes) envGen
    let ret_type = typeTToBlockYieldType type_'
    local (const ((envVar', envIter, envList), envProc, envGen')) (checkBlock ret_type False block)
    return envGen'

typeTToBlockYieldType :: TypeT -> BlockRetType
typeTToBlockYieldType type_ =
    case type_ of
        VoidT -> NoRetType
        type_' -> YieldType (typeTToType type_)

retValToTypeT :: RetVal -> TypeT
retValToTypeT retval = case retval of
    FunRetVoid_T _ -> VoidT
    FunRetVal_T _ type_ -> toTypeT type_

checkProcDef :: BNFC'Position -> RetVal -> Ident -> [Arg] -> Block -> RSET EnvProcT
checkProcDef pos retval ident args block = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (envVar', argTypes) <- insertArgsToEnvProc pos (envVar, []) args
    let type_ = retValToTypeT retval
    case M.lookup ident envProc of
        Just (type_', argTypes', False) -> do
            if type_' == type_ && argTypes' == argTypes
                then do
                    let envProc' = M.insert ident (type_', argTypes', True) envProc
                    let ret_type = typeTToBlockRetType type_'
                    local (const ((envVar', envIter, envList), envProc', envGen)) (checkBlock ret_type False block)
                    return envProc'
                else do
                    makeTypeError ("Procedure " ++ getIdentString ident ++ " is already defined with different type or arguments.") pos
        Just (type_', argTypes', True) -> do
            makeTypeError ("Procedure " ++ getIdentString ident ++ " is already defined.") pos
        _ -> do
            let envProc' = M.insert ident (type_, argTypes, True) envProc
            let ret_type = typeTToBlockRetType type_
            local (const ((envVar', envIter, envList), envProc', envGen)) (checkBlock ret_type False block)
            return envProc'

checkProcDecl :: BNFC'Position -> RetVal -> Ident -> [Arg] -> RSET EnvProcT
checkProcDecl pos retval ident args = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (envVar', argTypes) <- insertArgsToEnvProc pos (envVar, []) args
    let type_ = retValToTypeT retval
    case M.lookup ident envProc of
        Just (type_', argTypes', False) -> do
            if type_' == type_ && argTypes' == argTypes
                then do
                    let envProc' = M.insert ident (type_', argTypes', False) envProc
                    return envProc'
                else do
                    makeTypeError ("Procedure " ++ getIdentString ident ++ " is already defined with different type or arguments.") pos
        Just (type_', argTypes', True) -> do
            makeTypeError ("Procedure " ++ getIdentString ident ++ " is already defined.") pos
        _ -> do
            let envProc' = M.insert ident (type_, argTypes, False) envProc
            return envProc'

typeTToBlockRetType :: TypeT -> BlockRetType
typeTToBlockRetType type_ =
    case type_ of
        VoidT -> NoRetType
        type_' -> RetType (typeTToType type_)

insertArgsToEnvProc :: BNFC'Position -> (EnvVarT, [TypeT]) -> [Arg] -> RSET (EnvVarT, [TypeT])
insertArgsToEnvProc pos envVar [] = return envVar

insertArgsToEnvProc pos (envVar, argTypes) (arg : args) = do
    (storeVar, storeIter, stList) <- get
    let type_ = toTypeT (typeOfArg arg)
    let ident = getArgIdent arg
    let loc = getNewLocT storeVar
    let envVar' = M.insert ident loc envVar
    put (M.insert loc type_ storeVar, storeIter, stList)
    insertArgsToEnvProc pos (envVar', argTypes ++ [type_]) args

checkBlock :: BlockRetType -> Bool -> Block -> RSET ()
checkBlock ret_type can_break (Block_T pos stmts) = do
    checkStmts ret_type can_break stmts

checkStmts :: BlockRetType -> Bool -> [Stmt] -> RSET ()
checkStmts ret_type can_break [] = return ()

checkStmts ret_type can_break (stmt : stmts) = do
    case stmt of
        Decl_T pos type_ ident expr -> do
            env <- checkDecl pos type_ ident expr
            local (const env) (checkStmts ret_type can_break stmts)
        DeclGen_T pos ident1 ident2 args -> do
            env <- checkDeclIter pos ident1 ident2 args
            local (const env) (checkStmts ret_type can_break stmts)
        DeclList_T pos type_ ident1 exprs -> do
            env <- checkDeclList pos type_ ident1 exprs
            local (const env) (checkStmts ret_type can_break stmts)
        _no_decl -> do
            checkStmt ret_type can_break stmt
            checkStmts ret_type can_break stmts

checkDeclList :: BNFC'Position -> Type -> Ident -> [Expr] -> RSET EnvT
checkDeclList pos type_ ident exprs = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (storeVar, storeIter, stList) <- get
    let type_' = toTypeT type_
    let loc = getNewLocT storeVar
    let envList' = M.insert ident loc envList
    put (storeVar, storeIter, M.insert loc type_' stList)
    checkExprs pos exprs type_
    return ((envVar, envIter, envList'), envProc, envGen)

checkExprs :: BNFC'Position -> [Expr] -> Type -> RSET ()
checkExprs pos [] _type_ = return ()
checkExprs pos (ex : exs) type_ = do
    t <- checkExpr ex
    let t' = typeTToType t
    if stringTypeOfType t' == stringTypeOfType type_
        then checkExprs pos exs type_
        else makeTypeError
            ("Expression has type " ++
            stringTypeOfType t' ++
            " but should have type " ++
            stringTypeOfType type_)
            pos

checkDeclIter :: BNFC'Position -> Ident -> Ident -> [FunArg] -> RSET EnvT
checkDeclIter pos ident1 ident2 args = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (srVar, stIter, stList) <- get
    let loc = getNewLocIterT stIter
    let envIter' = M.insert ident1 loc envIter
    case M.lookup ident2 envGen of
        Nothing -> makeTypeError ("Generator " ++ getIdentString ident2 ++ " not found") pos
        Just (type_, argTypes) -> do
            checkArgs pos args argTypes
            put (srVar, M.insert loc type_ stIter, stList)
            return ((envVar, envIter', envList), envProc, envGen)

getNewLocT :: StoreVarT -> Loc
getNewLocT stVar =
  case M.keys stVar of
    [] -> 0
    keys -> maximum keys + 1

getNewLocIterT :: StoreIterT -> Loc
getNewLocIterT stIter =
  case M.keys stIter of
    [] -> 0
    keys -> maximum keys + 1

checkDecl :: BNFC'Position -> Type -> Ident -> Expr -> RSET EnvT
checkDecl pos type_ ident expr = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (storeVar, storeIter, stList) <- get
    typeExpr <- checkExpr expr
    let typeExpr' = typeTToType typeExpr
    if stringTypeOfType type_ == stringTypeOfType typeExpr'
        then do
            let loc = getNewLocT storeVar
            let envVar' = M.insert ident loc envVar
            put (M.insert loc (toTypeT type_) storeVar, storeIter, stList)
            return ((envVar', envIter, envList), envProc, envGen)
        else makeTypeError
            ("Variable " ++
            getIdentString ident ++
            " has type " ++
            stringTypeOfType typeExpr' ++
            " but should have type " ++
            stringTypeOfType type_)
            pos

checkStmt :: BlockRetType -> Bool -> Stmt -> RSET ()
checkStmt ret_type _can_break (Empty_T pos) = return ()

checkStmt ret_type can_break (Continue_T pos) = do
    if can_break
        then return ()
        else makeTypeError "Continue outside loop" pos

checkStmt ret_type can_break (Break_T pos) = do
    if can_break
        then return ()
        else makeTypeError "Break outside loop" pos

checkStmt ret_type can_break (BStmt_T pos block) = do
    checkBlock ret_type can_break block

checkStmt ret_type _can_break (Decl_T pos type_ ident expr) = undefined -- intended

checkStmt ret_type _can_break (Ass_T pos ident expr) = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (storeVar, _storeIter, _stList) <- get
    typeExpr <- checkExpr expr
    let typeExpr' = typeTToType typeExpr
    case M.lookup ident envVar of
        Nothing -> do
            makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
        Just loc -> case M.lookup loc storeVar of
            Nothing -> do
                makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
            Just type_ -> do
                let type_' = typeTToType type_
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

checkStmt ret_type _can_break (SExp_T pos expr) = do
    checkExpr expr
    return ()

checkStmt ret_type can_break (Cond_T pos expr block) = do
    type_ <- checkExpr expr
    let type_' = typeTToType type_
    if stringTypeOfType type_' == "bool"
        then checkBlock ret_type can_break block
        else makeTypeError
            ("Condition has type " ++
            stringTypeOfType type_' ++
            " but should have type bool")
            pos

checkStmt ret_type can_break (CondElse_T pos expr block1 block2) = do
    type_ <- checkExpr expr
    let type_' = typeTToType type_
    if stringTypeOfType type_' == "bool"
        then do
            checkBlock ret_type can_break block1
            checkBlock ret_type can_break block2
        else makeTypeError
            ("Condition has type " ++
            stringTypeOfType type_' ++
            " but should have type bool")
            pos

checkStmt ret_type can_break (While_T pos expr block) = do
    type_ <- checkExpr expr
    let type_' = typeTToType type_
    if stringTypeOfType type_' == "bool"
        then checkBlock ret_type True block
        else makeTypeError
            ("Condition has type " ++
            stringTypeOfType type_' ++
            " but should have type bool")
            pos

checkStmt ret_type can_break (ForGen_T pos ident1 ident2 funargs block) = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (storeVar, storeIter, stList) <- get
    -- check if generator exists
    case M.lookup ident2 envGen of
        Nothing -> makeTypeError ("Generator " ++ getIdentString ident2 ++ " not found") pos
        Just (type_, argTypes) -> do
            checkArgs pos funargs argTypes
            let loc = getNewLocT storeVar
            let envVar' = M.insert ident1 loc envVar
            put (M.insert loc type_ storeVar, storeIter, stList)
            local (const ((envVar', envIter, envList), envProc, envGen)) (checkBlock ret_type can_break block)

checkStmt ret_type _can_break (Incr_T pos ident) =
    checkIncrDecr pos ident

checkStmt ret_type _can_break (Decr_T pos ident) = do
    checkIncrDecr pos ident

checkStmt ret_type _can_break (Return_T pos expr) = do
    if ret_type == NoRetType
        then makeTypeError "Return in void function" pos
        else do
    type_ <- checkExpr expr
    let type_' = typeTToType type_
    retTypeT <- blockRetToTypeReturn pos ret_type
    let retType' = typeTToType retTypeT
    if stringTypeOfType type_' == stringTypeOfType retType'
        then return ()
        else makeTypeError
            ("Return has type " ++
            stringTypeOfType type_' ++
            " but should have type " ++
            stringTypeOfType retType')
            pos

checkStmt ret_type _can_break (Yield_T pos expr) = do
    type_ <- checkExpr expr
    let type_' = typeTToType type_
    retTypeT <- blockRetToTypeYield pos ret_type
    let retType' = typeTToType retTypeT
    if stringTypeOfType type_' == stringTypeOfType retType'
        then return ()
        else makeTypeError
            ("Yield has type " ++
            stringTypeOfType type_' ++
            " but should have type " ++
            stringTypeOfType retType')
            pos

checkStmt ret_type _can_break (DeclGen_T pos type_ ident expr) =
    undefined -- intended

checkStmt ret_type _can_break DeclList_T {} = undefined -- intended

checkStmt ret_type _can_break (PushToList_T pos ident expr) = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (storeVar, storeIter, stList) <- get
    typeExpr <- checkExpr expr
    let typeExpr' = typeTToType typeExpr
    case M.lookup ident envList of
        Nothing -> do
            makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
        Just loc -> case M.lookup loc stList of
            Nothing -> do
                makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
            Just type_ -> 
                if stringTypeOfType (typeTToType type_) == stringTypeOfType typeExpr'
                    then return ()
                    else makeTypeError
                        ("Variable " ++
                        getIdentString ident ++
                        " has type " ++
                        stringTypeOfType typeExpr' ++
                        " but should have type " ++
                        stringTypeOfType (typeTToType type_))
                        pos

checkStmt ret_type _can_break (PopFromList_T pos ident) = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (storeVar, storeIter, stList) <- get
    case M.lookup ident envList of
        Nothing -> do
            makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
        Just loc -> case M.lookup loc stList of 
            Nothing -> do
                makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
            Just type_ -> 
                return ()

checkStmt ret_type _can_break (AddToList_T pos ident expr1 expr2) = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (storeVar, storeIter, stList) <- get
    typeExpr <- checkExpr expr2
    let typeExpr' = typeTToType typeExpr
    case M.lookup ident envList of
        Nothing -> do
            makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
        Just loc -> case M.lookup loc stList of
            Nothing -> do
                makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
            Just type_ -> 
                if stringTypeOfType (typeTToType type_) == stringTypeOfType typeExpr'
                    then return ()
                    else do 
                        typeExpr1 <- checkExpr expr1
                        let typeExpr1' = typeTToType typeExpr1
                        if "int" == stringTypeOfType typeExpr'
                            then return ()
                            else makeTypeError "Index type mismatch" pos

checkStmt ret_type _can_break (RemoveFromList_T pos ident expr) = do 
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (storeVar, storeIter, stList) <- get
    typeExpr <- checkExpr expr
    let typeExpr' = typeTToType typeExpr
    case M.lookup ident envList of
        Nothing -> do
            makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
        Just loc -> case M.lookup loc stList of
            Nothing -> do
                makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
            Just type_ -> 
                if "int" == stringTypeOfType typeExpr'
                    then return ()
                    else makeTypeError "Index type mismatch" pos
    

blockRetToTypeReturn :: BNFC'Position -> BlockRetType -> RSET TypeT
blockRetToTypeReturn pos (RetType type_) = return (toTypeT type_)
blockRetToTypeReturn pos NoRetType = return VoidT
blockRetToTypeReturn pos _ = makeTypeError "Return in generator" pos

blockRetToTypeYield :: BNFC'Position -> BlockRetType -> RSET TypeT
blockRetToTypeYield pos (YieldType type_) = return (toTypeT type_)
blockRetToTypeYield pos NoRetType = return VoidT
blockRetToTypeYield pos _ = makeTypeError "Yield outside generator" pos

checkIncrDecr :: BNFC'Position -> Ident -> RSET ()
checkIncrDecr pos ident = do
    ((envVar, _envIter, _envList), _envProc, _envGen) <- ask
    (storeVar, _storeIter, _stList) <- get
    case M.lookup ident envVar of
        Nothing -> do
            makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
        Just loc -> case M.lookup loc storeVar of
            Nothing -> do
                makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
            Just type_ -> do
                let type_' = typeTToType type_
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
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (storeVar, storeIter, stList) <- get
    typeExpr <- checkExpr expr
    let typeExpr' = typeTToType typeExpr
    if stringTypeOfType type_ == stringTypeOfType typeExpr'
        then do
            let loc = getNewLocT storeVar
            let envVar' = M.insert ident loc envVar
            put (M.insert loc (toTypeT type_) storeVar, storeIter, stList)
            return ((envVar', envIter, envList), envProc, envGen)
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

checkExpr :: Expr -> RSET TypeT
checkExpr (EVar_T pos var) = do
    ((envVar, _envIter, envList), _envProc, _envGen) <- ask
    (storeVar, _storeIter, _stList) <- get
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
    let typeExpr' = typeTToType typeExpr
    if  stringTypeOfType typeExpr' == "int"
        then return IntT
        else makeTypeError "Expression should be of type int" pos

checkExpr (Not_T pos expr) = do
    typeExpr <- checkExpr expr
    let typeExpr' = typeTToType typeExpr
    if  stringTypeOfType typeExpr' == "bool"
        then return BoolT
        else makeTypeError "Expression should be of type bool" pos

checkExpr (EMul_T pos expr1 mulop expr2) = do
    typeExpr1 <- checkExpr expr1
    typeExpr2 <- checkExpr expr2
    let typeExpr1' = typeTToType typeExpr1
    if  stringTypeOfType typeExpr1' == "int"
        then do
            let typeExpr2' = typeTToType typeExpr2
            if  stringTypeOfType typeExpr2' == "int"
                then return IntT
                else makeTypeError "Expression should be of type int" pos
        else makeTypeError ("Expression" ++ " should be of type int") pos

checkExpr (EAdd_T pos expr1 addop expr2) = do
    typeExpr1 <- checkExpr expr1
    let typeExpr1' = typeTToType typeExpr1
    typeExpr2 <- checkExpr expr2
    let typeExpr2' = typeTToType typeExpr2
    let typeStr1 = stringTypeOfType typeExpr1'
    let typeStr2 = stringTypeOfType typeExpr2'
    case (typeStr1, typeStr2) of
        ("int", "int") -> return IntT
        ("string", "string") -> return StrT
        _ -> makeTypeError "Add expression should be of type int or string" pos

checkExpr (ERel_T pos expr1 relop expr2) = do
    typeExpr1 <- checkExpr expr1
    let typeExpr1' = typeTToType typeExpr1
    if  stringTypeOfType typeExpr1' == "int"
        then do
            typeExpr2 <- checkExpr expr2
            let typeExpr2' = typeTToType typeExpr2
            if  stringTypeOfType typeExpr2' == "int"
                then return BoolT
                else makeTypeError "Expression should be of type int" pos
        else
            if  stringTypeOfType typeExpr1' == "string" then
                case relop of
                    EQU_T _ -> do
                        typeExpr2 <- checkExpr expr2
                        let typeExpr2' = typeTToType typeExpr2
                        if  stringTypeOfType typeExpr2' == "string"
                            then return BoolT
                            else makeTypeError "Expression should be of type string" pos
                    NE_T _ -> do
                        typeExpr2 <- checkExpr expr2
                        let typeExpr2' = typeTToType typeExpr2
                        if  stringTypeOfType typeExpr2' == "string"
                            then return BoolT
                            else makeTypeError "Expression should be of type string" pos
                    _ -> makeTypeError "Wrong expression type" pos
            else
                makeTypeError "Wrong expression type" pos

checkExpr (EAnd_T pos expr1 expr2) = do
    typeExpr1 <- checkExpr expr1
    let typeExpr1' = typeTToType typeExpr1
    if  stringTypeOfType typeExpr1' == "bool"
        then do
            typeExpr2 <- checkExpr expr2
            let typeExpr2' = typeTToType typeExpr2
            if  stringTypeOfType typeExpr2' == "bool"
                then return BoolT
                else makeTypeError "Expression should be of type bool" pos
        else makeTypeError ("Expression" ++ " should be of type bool") pos

checkExpr (EOr_T pos expr1 expr2) = do
    typeExpr1 <- checkExpr expr1
    let typeExpr1' = typeTToType typeExpr1
    if  stringTypeOfType typeExpr1' == "bool"
        then do
            typeExpr2 <- checkExpr expr2
            let typeExpr2' = typeTToType typeExpr2
            if  stringTypeOfType typeExpr2' == "bool"
                then return BoolT
                else makeTypeError "Expression should be of type bool" pos
        else makeTypeError ("Expression" ++ " should be of type bool") pos

checkExpr (ECast_T pos type_ expr) = do
    typeExpr <- checkExpr expr
    let typeExpr' = typeTToType typeExpr
    case (stringTypeOfType typeExpr', type_) of
        ("int", Int_T _) -> return IntT
        ("int", CharT_T _) -> return CharT
        ("int", Str_T _) -> return StrT
        ("int", Bool_T _) -> return BoolT
        ("char", Int_T _) -> return IntT
        ("char", CharT_T _) -> return CharT
        ("char", Str_T _) -> return StrT
        ("string", Str_T _) -> return StrT
        ("bool", Int_T _) -> return IntT
        ("bool", Str_T _) -> return StrT
        ("bool", Bool_T _) -> return BoolT
        _ -> makeTypeError ("Cannot cast " ++ stringTypeOfType typeExpr' ++ " to " ++ stringTypeOfType type_) pos

checkExpr (EGenNext_T pos ident) = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (stVar, stIter, stList) <- get
    case M.lookup ident envIter of
        Nothing -> makeTypeError ("Iterator " ++ getIdentString ident ++ " not declared") pos
        Just loc -> do
            case M.lookup loc stIter of
                Nothing -> makeTypeError ("Iterator " ++ getIdentString ident ++ " not defined") pos
                Just type_ -> return type_

checkExpr (App_T pos ident funargs) = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
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
        Just (type_, argsTypes, _) -> do
            checkArgs pos funargs argsTypes
            return type_

checkExpr (EListElem_T pos ident expr) = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (storeVar, storeIter, stList) <- get
    typeExpr <- checkExpr expr
    let typeExpr' = typeTToType typeExpr
    case M.lookup ident envList of 
        Nothing -> do
            makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
        Just loc -> case M.lookup loc stList of
            Nothing -> do
                makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
            Just type_ -> 
                if "int" == stringTypeOfType typeExpr'
                    then return type_
                    else makeTypeError "Index type mismatch" pos

checkExpr (EListLen_T pos ident) = do
    ((envVar, envIter, envList), envProc, envGen) <- ask
    (storeVar, storeIter, stList) <- get
    case M.lookup ident envList of 
        Nothing -> do
            makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
        Just loc -> case M.lookup loc stList of
            Nothing -> do
                makeTypeError ("Variable " ++ getIdentString ident ++ " undefined") pos
            Just type_ -> 
                return IntT

checkArgs :: BNFC'Position -> [FunArg] -> [TypeT] -> RSET ()
checkArgs pos [] [] = return ()

checkArgs pos (farg : fargs) (argT : argsT) = do
    case farg of
        AsValue_T pos expr -> do
            typeExpr <- checkExpr expr
            let typeExpr' = typeTToType typeExpr
            let argT' = typeTToType argT
            if  stringTypeOfType typeExpr' == stringTypeOfType argT'
                then checkArgs pos fargs argsT
                else
                    makeTypeError
                        ("Argument should be of type " ++
                        stringTypeOfType argT') pos
        AsRef_T pos var -> do
            let ident = getVarIdent var
            ((envVar, envIter, _envList), envProc, envGen) <- ask
            (storeVar, storeIter, stList) <- get
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
                            let typeOfArg_ = typeTToType typeT_
                            let argT' = typeTToType argT
                            if  stringTypeOfType typeOfArg_ == stringTypeOfType argT'
                                then checkArgs pos fargs argsT
                                else
                                    makeTypeError
                                        ("Argument should be of type " ++
                                        stringTypeOfType argT') pos

checkArgs pos _ _ = makeTypeError "Wrong number of arguments" pos

typeTToType :: TypeT -> Type
typeTToType type_ = case type_ of
    IntT -> Int_T Nothing
    CharT -> CharT_T Nothing
    StrT -> Str_T Nothing
    BoolT -> Bool_T Nothing
    VoidT -> undefined -- intended