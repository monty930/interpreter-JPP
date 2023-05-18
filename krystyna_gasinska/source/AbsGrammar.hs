-- File generated by the BNF Converter (bnfc 2.9.4.1).

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

-- | The abstract syntax of language grammar.

module AbsGrammar where

import Prelude (Char, Integer, String)
import qualified Prelude as C
  ( Eq, Ord, Show, Read
  , Functor, Foldable, Traversable
  , Int, Maybe(..)
  )
import qualified Data.String

type Program = Program' BNFC'Position
data Program' a = Program_T a [TopDef' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type TopDef = TopDef' BNFC'Position
data TopDef' a
    = ProcDef_T a (RetVal' a) Ident [Arg' a] (Block' a)
    | GlobVar_T a (Type' a) Ident (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Arg = Arg' BNFC'Position
data Arg' a = Arg_T a (Type' a) Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Block = Block' BNFC'Position
data Block' a = Block_T a [Stmt' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Stmt = Stmt' BNFC'Position
data Stmt' a
    = Empty_T a
    | BStmt_T a (Block' a)
    | Decl_T a (Type' a) Ident (Expr' a)
    | Ass_T a Ident (Expr' a)
    | Incr_T a Ident
    | Decr_T a Ident
    | Cond_T a (Expr' a) (Block' a)
    | CondElse_T a (Expr' a) (Block' a) (Block' a)
    | While_T a (Expr' a) (Block' a)
    | App_T a Ident [FunArg' a]
    | Return_T a (Expr' a)
    | SExp_T a (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Type = Type' BNFC'Position
data Type' a = Int_T a | CharT_T a | Str_T a | Bool_T a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type RetVal = RetVal' BNFC'Position
data RetVal' a = FunRetVal_T a (Type' a) | FunRetVoid_T a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Var = Var' BNFC'Position
data Var' a = Var_T a Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Expr = Expr' BNFC'Position
data Expr' a
    = EVar_T a (Var' a)
    | ELit_T a (ELit' a)
    | Neg_T a (Expr' a)
    | Not_T a (Expr' a)
    | EMul_T a (Expr' a) (MulOp' a) (Expr' a)
    | EAdd_T a (Expr' a) (AddOp' a) (Expr' a)
    | ERel_T a (Expr' a) (RelOp' a) (Expr' a)
    | EAnd_T a (Expr' a) (Expr' a)
    | EOr_T a (Expr' a) (Expr' a)
    | ECast_T a (Type' a) (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type ELit = ELit' BNFC'Position
data ELit' a
    = ELitInt_T a Integer
    | ELitBool_T a (EBool' a)
    | EString_T a String
    | EChar_T a Char
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type EBool = EBool' BNFC'Position
data EBool' a = ELitTrue_T a | ELitFalse_T a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type FunArg = FunArg' BNFC'Position
data FunArg' a = AsValue_T a (Expr' a) | AsRef_T a (Var' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type AddOp = AddOp' BNFC'Position
data AddOp' a = Plus_T a | Minus_T a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type MulOp = MulOp' BNFC'Position
data MulOp' a = Times_T a | Div_T a | Mod_T a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type RelOp = RelOp' BNFC'Position
data RelOp' a
    = LTH_T a | LE_T a | GTH_T a | GE_T a | EQU_T a | NE_T a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

newtype Ident = Ident String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

-- | Start position (line, column) of something.

type BNFC'Position = C.Maybe (C.Int, C.Int)

pattern BNFC'NoPosition :: BNFC'Position
pattern BNFC'NoPosition = C.Nothing

pattern BNFC'Position :: C.Int -> C.Int -> BNFC'Position
pattern BNFC'Position line col = C.Just (line, col)

-- | Get the start position of something.

class HasPosition a where
  hasPosition :: a -> BNFC'Position

instance HasPosition Program where
  hasPosition = \case
    Program_T p _ -> p

instance HasPosition TopDef where
  hasPosition = \case
    ProcDef_T p _ _ _ _ -> p
    GlobVar_T p _ _ _ -> p

instance HasPosition Arg where
  hasPosition = \case
    Arg_T p _ _ -> p

instance HasPosition Block where
  hasPosition = \case
    Block_T p _ -> p

instance HasPosition Stmt where
  hasPosition = \case
    Empty_T p -> p
    BStmt_T p _ -> p
    Decl_T p _ _ _ -> p
    Ass_T p _ _ -> p
    Incr_T p _ -> p
    Decr_T p _ -> p
    Cond_T p _ _ -> p
    CondElse_T p _ _ _ -> p
    While_T p _ _ -> p
    App_T p _ _ -> p
    Return_T p _ -> p
    SExp_T p _ -> p

instance HasPosition Type where
  hasPosition = \case
    Int_T p -> p
    CharT_T p -> p
    Str_T p -> p
    Bool_T p -> p

instance HasPosition RetVal where
  hasPosition = \case
    FunRetVal_T p _ -> p
    FunRetVoid_T p -> p

instance HasPosition Var where
  hasPosition = \case
    Var_T p _ -> p

instance HasPosition Expr where
  hasPosition = \case
    EVar_T p _ -> p
    ELit_T p _ -> p
    Neg_T p _ -> p
    Not_T p _ -> p
    EMul_T p _ _ _ -> p
    EAdd_T p _ _ _ -> p
    ERel_T p _ _ _ -> p
    EAnd_T p _ _ -> p
    EOr_T p _ _ -> p
    ECast_T p _ _ -> p

instance HasPosition ELit where
  hasPosition = \case
    ELitInt_T p _ -> p
    ELitBool_T p _ -> p
    EString_T p _ -> p
    EChar_T p _ -> p

instance HasPosition EBool where
  hasPosition = \case
    ELitTrue_T p -> p
    ELitFalse_T p -> p

instance HasPosition FunArg where
  hasPosition = \case
    AsValue_T p _ -> p
    AsRef_T p _ -> p

instance HasPosition AddOp where
  hasPosition = \case
    Plus_T p -> p
    Minus_T p -> p

instance HasPosition MulOp where
  hasPosition = \case
    Times_T p -> p
    Div_T p -> p
    Mod_T p -> p

instance HasPosition RelOp where
  hasPosition = \case
    LTH_T p -> p
    LE_T p -> p
    GTH_T p -> p
    GE_T p -> p
    EQU_T p -> p
    NE_T p -> p

