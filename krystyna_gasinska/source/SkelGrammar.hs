-- File generated by the BNF Converter (bnfc 2.9.4.1).

-- Templates for pattern matching on abstract syntax

{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module SkelGrammar where

import Prelude (($), Either(..), String, (++), Show, show)
import qualified AbsGrammar

type Err = Either String
type Result = Err String

failure :: Show a => a -> Result
failure x = Left $ "Undefined case: " ++ show x

transIdent :: AbsGrammar.Ident -> Result
transIdent x = case x of
  AbsGrammar.Ident string -> failure x

transProgram :: Show a => AbsGrammar.Program' a -> Result
transProgram x = case x of
  AbsGrammar.Program_T _ topdefs -> failure x

transTopDef :: Show a => AbsGrammar.TopDef' a -> Result
transTopDef x = case x of
  AbsGrammar.ProcDef_T _ retval ident args block -> failure x
  AbsGrammar.GlobVar_T _ type_ ident expr -> failure x

transArg :: Show a => AbsGrammar.Arg' a -> Result
transArg x = case x of
  AbsGrammar.Arg_T _ type_ ident -> failure x

transBlock :: Show a => AbsGrammar.Block' a -> Result
transBlock x = case x of
  AbsGrammar.Block_T _ stmts -> failure x

transStmt :: Show a => AbsGrammar.Stmt' a -> Result
transStmt x = case x of
  AbsGrammar.Empty_T _ -> failure x
  AbsGrammar.BStmt_T _ block -> failure x
  AbsGrammar.Decl_T _ type_ ident expr -> failure x
  AbsGrammar.Ass_T _ ident expr -> failure x
  AbsGrammar.Incr_T _ ident -> failure x
  AbsGrammar.Decr_T _ ident -> failure x
  AbsGrammar.Cond_T _ expr block -> failure x
  AbsGrammar.CondElse_T _ expr block1 block2 -> failure x
  AbsGrammar.While_T _ expr block -> failure x
  AbsGrammar.App_T _ ident funargs -> failure x
  AbsGrammar.Return_T _ expr -> failure x
  AbsGrammar.SExp_T _ expr -> failure x

transType :: Show a => AbsGrammar.Type' a -> Result
transType x = case x of
  AbsGrammar.Int_T _ -> failure x
  AbsGrammar.CharT_T _ -> failure x
  AbsGrammar.Str_T _ -> failure x
  AbsGrammar.Bool_T _ -> failure x

transRetVal :: Show a => AbsGrammar.RetVal' a -> Result
transRetVal x = case x of
  AbsGrammar.FunRetVal_T _ type_ -> failure x
  AbsGrammar.FunRetVoid_T _ -> failure x

transVar :: Show a => AbsGrammar.Var' a -> Result
transVar x = case x of
  AbsGrammar.Var_T _ ident -> failure x

transExpr :: Show a => AbsGrammar.Expr' a -> Result
transExpr x = case x of
  AbsGrammar.EVar_T _ var -> failure x
  AbsGrammar.ELit_T _ elit -> failure x
  AbsGrammar.Neg_T _ expr -> failure x
  AbsGrammar.Not_T _ expr -> failure x
  AbsGrammar.EMul_T _ expr1 mulop expr2 -> failure x
  AbsGrammar.EAdd_T _ expr1 addop expr2 -> failure x
  AbsGrammar.ERel_T _ expr1 relop expr2 -> failure x
  AbsGrammar.EAnd_T _ expr1 expr2 -> failure x
  AbsGrammar.EOr_T _ expr1 expr2 -> failure x
  AbsGrammar.ECast_T _ type_ expr -> failure x

transELit :: Show a => AbsGrammar.ELit' a -> Result
transELit x = case x of
  AbsGrammar.ELitInt_T _ integer -> failure x
  AbsGrammar.ELitBool_T _ ebool -> failure x
  AbsGrammar.EString_T _ string -> failure x
  AbsGrammar.EChar_T _ char -> failure x

transEBool :: Show a => AbsGrammar.EBool' a -> Result
transEBool x = case x of
  AbsGrammar.ELitTrue_T _ -> failure x
  AbsGrammar.ELitFalse_T _ -> failure x

transFunArg :: Show a => AbsGrammar.FunArg' a -> Result
transFunArg x = case x of
  AbsGrammar.AsValue_T _ expr -> failure x
  AbsGrammar.AsRef_T _ var -> failure x

transAddOp :: Show a => AbsGrammar.AddOp' a -> Result
transAddOp x = case x of
  AbsGrammar.Plus_T _ -> failure x
  AbsGrammar.Minus_T _ -> failure x

transMulOp :: Show a => AbsGrammar.MulOp' a -> Result
transMulOp x = case x of
  AbsGrammar.Times_T _ -> failure x
  AbsGrammar.Div_T _ -> failure x
  AbsGrammar.Mod_T _ -> failure x

transRelOp :: Show a => AbsGrammar.RelOp' a -> Result
transRelOp x = case x of
  AbsGrammar.LTH_T _ -> failure x
  AbsGrammar.LE_T _ -> failure x
  AbsGrammar.GTH_T _ -> failure x
  AbsGrammar.GE_T _ -> failure x
  AbsGrammar.EQU_T _ -> failure x
  AbsGrammar.NE_T _ -> failure x
