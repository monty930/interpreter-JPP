-- -*- haskell -*- File generated by the BNF Converter (bnfc 2.9.4.1).

-- Parser definition for use with Happy
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module ParGrammar
  ( happyError
  , myLexer
  , pProgram
  ) where

import Prelude

import qualified AbsGrammar
import LexGrammar

}

%name pProgram_internal Program
-- no lexer declaration
%monad { Err } { (>>=) } { return }
%tokentype {Token}
%token
  '!'        { PT _ (TS _ 1)  }
  '!='       { PT _ (TS _ 2)  }
  '%'        { PT _ (TS _ 3)  }
  '&'        { PT _ (TS _ 4)  }
  '&&'       { PT _ (TS _ 5)  }
  '('        { PT _ (TS _ 6)  }
  ')'        { PT _ (TS _ 7)  }
  ').('      { PT _ (TS _ 8)  }
  '*'        { PT _ (TS _ 9)  }
  '+'        { PT _ (TS _ 10) }
  '++'       { PT _ (TS _ 11) }
  ','        { PT _ (TS _ 12) }
  '-'        { PT _ (TS _ 13) }
  '--'       { PT _ (TS _ 14) }
  '.add'     { PT _ (TS _ 15) }
  '.pop'     { PT _ (TS _ 16) }
  '.push'    { PT _ (TS _ 17) }
  '.remove'  { PT _ (TS _ 18) }
  '/'        { PT _ (TS _ 19) }
  ';'        { PT _ (TS _ 20) }
  '<'        { PT _ (TS _ 21) }
  '<='       { PT _ (TS _ 22) }
  '='        { PT _ (TS _ 23) }
  '=='       { PT _ (TS _ 24) }
  '>'        { PT _ (TS _ 25) }
  '>='       { PT _ (TS _ 26) }
  'Gen'      { PT _ (TS _ 27) }
  'Glob'     { PT _ (TS _ 28) }
  'Proc'     { PT _ (TS _ 29) }
  '['        { PT _ (TS _ 30) }
  ']'        { PT _ (TS _ 31) }
  'bool'     { PT _ (TS _ 32) }
  'break'    { PT _ (TS _ 33) }
  'char'     { PT _ (TS _ 34) }
  'continue' { PT _ (TS _ 35) }
  'else'     { PT _ (TS _ 36) }
  'false'    { PT _ (TS _ 37) }
  'for'      { PT _ (TS _ 38) }
  'gen'      { PT _ (TS _ 39) }
  'if'       { PT _ (TS _ 40) }
  'in'       { PT _ (TS _ 41) }
  'int'      { PT _ (TS _ 42) }
  'list'     { PT _ (TS _ 43) }
  'next'     { PT _ (TS _ 44) }
  'return'   { PT _ (TS _ 45) }
  'string'   { PT _ (TS _ 46) }
  'true'     { PT _ (TS _ 47) }
  'while'    { PT _ (TS _ 48) }
  'yield'    { PT _ (TS _ 49) }
  '{'        { PT _ (TS _ 50) }
  '||'       { PT _ (TS _ 51) }
  '}'        { PT _ (TS _ 52) }
  L_Ident    { PT _ (TV _)    }
  L_charac   { PT _ (TC _)    }
  L_integ    { PT _ (TI _)    }
  L_quoted   { PT _ (TL _)    }

%%

Ident :: { (AbsGrammar.BNFC'Position, AbsGrammar.Ident) }
Ident  : L_Ident { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Ident (tokenText $1)) }

Char    :: { (AbsGrammar.BNFC'Position, Char) }
Char     : L_charac { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), (read (tokenText $1)) :: Char) }

Integer :: { (AbsGrammar.BNFC'Position, Integer) }
Integer  : L_integ  { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), (read (tokenText $1)) :: Integer) }

String  :: { (AbsGrammar.BNFC'Position, String) }
String   : L_quoted { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), ((\(PT _ (TL s)) -> s) $1)) }

Program :: { (AbsGrammar.BNFC'Position, AbsGrammar.Program) }
Program
  : ListTopDef { (fst $1, AbsGrammar.Program_T (fst $1) (snd $1)) }

TopDef :: { (AbsGrammar.BNFC'Position, AbsGrammar.TopDef) }
TopDef
  : RetVal Ident '(' ListArg ')' ';' { (fst $1, AbsGrammar.ProcDecl_T (fst $1) (snd $1) (snd $2) (snd $4)) }
  | RetVal Ident '(' ListArg ')' Block { (fst $1, AbsGrammar.ProcDef_T (fst $1) (snd $1) (snd $2) (snd $4) (snd $6)) }
  | 'Glob' Type Ident '=' Expr ';' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.GlobVar_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $3) (snd $5)) }
  | 'Gen' Type Ident '(' ListArg ')' Block { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Gener_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $3) (snd $5) (snd $7)) }

ListTopDef :: { (AbsGrammar.BNFC'Position, [AbsGrammar.TopDef]) }
ListTopDef
  : {- empty -} { (AbsGrammar.BNFC'NoPosition, []) }
  | TopDef ListTopDef { (fst $1, (:) (snd $1) (snd $2)) }

Arg :: { (AbsGrammar.BNFC'Position, AbsGrammar.Arg) }
Arg
  : Type Ident { (fst $1, AbsGrammar.Arg_T (fst $1) (snd $1) (snd $2)) }
  | 'list' Ident { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.ArgList_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $2)) }

ListArg :: { (AbsGrammar.BNFC'Position, [AbsGrammar.Arg]) }
ListArg
  : {- empty -} { (AbsGrammar.BNFC'NoPosition, []) }
  | Arg { (fst $1, (:[]) (snd $1)) }
  | Arg ',' ListArg { (fst $1, (:) (snd $1) (snd $3)) }

Block :: { (AbsGrammar.BNFC'Position, AbsGrammar.Block) }
Block
  : '{' ListStmt '}' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Block_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $2)) }

ListStmt :: { (AbsGrammar.BNFC'Position, [AbsGrammar.Stmt]) }
ListStmt
  : {- empty -} { (AbsGrammar.BNFC'NoPosition, []) }
  | Stmt ListStmt { (fst $1, (:) (snd $1) (snd $2)) }

Stmt :: { (AbsGrammar.BNFC'Position, AbsGrammar.Stmt) }
Stmt
  : ';' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Empty_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | Block { (fst $1, AbsGrammar.BStmt_T (fst $1) (snd $1)) }
  | Type Ident '=' Expr ';' { (fst $1, AbsGrammar.Decl_T (fst $1) (snd $1) (snd $2) (snd $4)) }
  | Ident '=' Expr ';' { (fst $1, AbsGrammar.Ass_T (fst $1) (snd $1) (snd $3)) }
  | Ident '++' ';' { (fst $1, AbsGrammar.Incr_T (fst $1) (snd $1)) }
  | Ident '--' ';' { (fst $1, AbsGrammar.Decr_T (fst $1) (snd $1)) }
  | 'break' ';' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Break_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | 'continue' ';' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Continue_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | 'if' '(' Expr ')' Block { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Cond_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $5)) }
  | 'if' '(' Expr ')' Block 'else' Block { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.CondElse_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $5) (snd $7)) }
  | 'while' '(' Expr ')' Block { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.While_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $5)) }
  | 'return' '(' Expr ')' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Return_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $3)) }
  | 'yield' '(' Expr ')' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Yield_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $3)) }
  | 'gen' Ident '=' Ident '(' ListFunArg ')' ';' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.DeclGen_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $4) (snd $6)) }
  | 'for' '(' Ident 'in' Ident '(' ListFunArg ')' ')' Block { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.ForGen_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $5) (snd $7) (snd $10)) }
  | 'list' Type Ident '=' '[' ListExpr ']' ';' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.DeclList_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $3) (snd $6)) }
  | Ident '.push' '(' Expr ')' ';' { (fst $1, AbsGrammar.PushToList_T (fst $1) (snd $1) (snd $4)) }
  | Ident '.pop' ';' { (fst $1, AbsGrammar.PopFromList_T (fst $1) (snd $1)) }
  | Ident '.add' '(' Expr ').(' Expr ')' ';' { (fst $1, AbsGrammar.AddToList_T (fst $1) (snd $1) (snd $4) (snd $6)) }
  | Ident '.remove' '(' Expr ')' ';' { (fst $1, AbsGrammar.RemoveFromList_T (fst $1) (snd $1) (snd $4)) }
  | Expr ';' { (fst $1, AbsGrammar.SExp_T (fst $1) (snd $1)) }

Type :: { (AbsGrammar.BNFC'Position, AbsGrammar.Type) }
Type
  : 'int' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Int_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | 'char' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.CharT_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | 'string' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Str_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | 'bool' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Bool_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }

RetVal :: { (AbsGrammar.BNFC'Position, AbsGrammar.RetVal) }
RetVal
  : Type { (fst $1, AbsGrammar.FunRetVal_T (fst $1) (snd $1)) }
  | 'Proc' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.FunRetVoid_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }

Var :: { (AbsGrammar.BNFC'Position, AbsGrammar.Var) }
Var : Ident { (fst $1, AbsGrammar.Var_T (fst $1) (snd $1)) }

Expr7 :: { (AbsGrammar.BNFC'Position, AbsGrammar.Expr) }
Expr7
  : Ident '[' Expr ']' { (fst $1, AbsGrammar.EListElem_T (fst $1) (snd $1) (snd $3)) }
  | Var { (fst $1, AbsGrammar.EVar_T (fst $1) (snd $1)) }
  | ELit { (fst $1, AbsGrammar.ELit_T (fst $1) (snd $1)) }
  | Ident '(' ListFunArg ')' { (fst $1, AbsGrammar.App_T (fst $1) (snd $1) (snd $3)) }
  | '(' Expr ')' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), (snd $2)) }

ELit :: { (AbsGrammar.BNFC'Position, AbsGrammar.ELit) }
ELit
  : Integer { (fst $1, AbsGrammar.ELitInt_T (fst $1) (snd $1)) }
  | EBool { (fst $1, AbsGrammar.ELitBool_T (fst $1) (snd $1)) }
  | String { (fst $1, AbsGrammar.EString_T (fst $1) (snd $1)) }
  | Char { (fst $1, AbsGrammar.EChar_T (fst $1) (snd $1)) }

EBool :: { (AbsGrammar.BNFC'Position, AbsGrammar.EBool) }
EBool
  : 'true' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.ELitTrue_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | 'false' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.ELitFalse_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }

FunArg :: { (AbsGrammar.BNFC'Position, AbsGrammar.FunArg) }
FunArg
  : Expr { (fst $1, AbsGrammar.AsValue_T (fst $1) (snd $1)) }
  | '&' Var { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.AsRef_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $2)) }

ListFunArg :: { (AbsGrammar.BNFC'Position, [AbsGrammar.FunArg]) }
ListFunArg
  : {- empty -} { (AbsGrammar.BNFC'NoPosition, []) }
  | FunArg { (fst $1, (:[]) (snd $1)) }
  | FunArg ',' ListFunArg { (fst $1, (:) (snd $1) (snd $3)) }

Expr6 :: { (AbsGrammar.BNFC'Position, AbsGrammar.Expr) }
Expr6
  : '-' Expr7 { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Neg_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | '!' Expr7 { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Not_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | '(' Type ')' Expr6 { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.ECast_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $4)) }
  | 'next' '(' Ident ')' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.EGenNext_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1)) (snd $3)) }
  | Expr7 { (fst $1, (snd $1)) }

Expr5 :: { (AbsGrammar.BNFC'Position, AbsGrammar.Expr) }
Expr5
  : Expr5 MulOp Expr6 { (fst $1, AbsGrammar.EMul_T (fst $1) (snd $1) (snd $2) (snd $3)) }
  | Expr6 { (fst $1, (snd $1)) }

Expr4 :: { (AbsGrammar.BNFC'Position, AbsGrammar.Expr) }
Expr4
  : Expr4 AddOp Expr5 { (fst $1, AbsGrammar.EAdd_T (fst $1) (snd $1) (snd $2) (snd $3)) }
  | Expr5 { (fst $1, (snd $1)) }

Expr3 :: { (AbsGrammar.BNFC'Position, AbsGrammar.Expr) }
Expr3
  : Expr3 RelOp Expr4 { (fst $1, AbsGrammar.ERel_T (fst $1) (snd $1) (snd $2) (snd $3)) }
  | Expr4 { (fst $1, (snd $1)) }

Expr2 :: { (AbsGrammar.BNFC'Position, AbsGrammar.Expr) }
Expr2
  : Expr3 '&&' Expr2 { (fst $1, AbsGrammar.EAnd_T (fst $1) (snd $1) (snd $3)) }
  | Expr3 { (fst $1, (snd $1)) }

Expr1 :: { (AbsGrammar.BNFC'Position, AbsGrammar.Expr) }
Expr1
  : Expr2 '||' Expr1 { (fst $1, AbsGrammar.EOr_T (fst $1) (snd $1) (snd $3)) }
  | Expr2 { (fst $1, (snd $1)) }

Expr :: { (AbsGrammar.BNFC'Position, AbsGrammar.Expr) }
Expr : Expr1 { (fst $1, (snd $1)) }

ListExpr :: { (AbsGrammar.BNFC'Position, [AbsGrammar.Expr]) }
ListExpr
  : {- empty -} { (AbsGrammar.BNFC'NoPosition, []) }
  | Expr { (fst $1, (:[]) (snd $1)) }
  | Expr ',' ListExpr { (fst $1, (:) (snd $1) (snd $3)) }

AddOp :: { (AbsGrammar.BNFC'Position, AbsGrammar.AddOp) }
AddOp
  : '+' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Plus_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | '-' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Minus_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }

MulOp :: { (AbsGrammar.BNFC'Position, AbsGrammar.MulOp) }
MulOp
  : '*' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Times_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | '/' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Div_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | '%' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.Mod_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }

RelOp :: { (AbsGrammar.BNFC'Position, AbsGrammar.RelOp) }
RelOp
  : '<' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.LTH_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | '<=' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.LE_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | '>' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.GTH_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | '>=' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.GE_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | '==' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.EQU_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }
  | '!=' { (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1), AbsGrammar.NE_T (uncurry AbsGrammar.BNFC'Position (tokenLineCol $1))) }

{

type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens

-- Entrypoints

pProgram :: [Token] -> Err AbsGrammar.Program
pProgram = fmap snd . pProgram_internal
}

