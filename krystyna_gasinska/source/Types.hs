module Types where

import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import AbsGrammar
import LexGrammar   ( Token, mkPosToken )
import ParGrammar   ( pProgram, myLexer )
import PrintGrammar ( Print, printTree )
import SkelGrammar

type Loc = Int

type EnvVar = M.Map Ident Loc

type StoreVar = M.Map Loc (Type, ELit)

type StoreList = M.Map Loc [ELit]

type EnvIter = M.Map Ident Loc

type EnvList = M.Map Ident Loc

type StoreIter = M.Map Loc (Type, GenState, EnvSt)

type EnvProc = M.Map Ident (RetVal, [Arg], Block, EnvSt, Bool)

type EnvGen = M.Map Ident (Type, [Arg], Block, EnvSt)

type EnvSt = (EnvVar, EnvIter, EnvList)

type Env = (EnvSt, EnvProc, EnvGen)

type Store = (StoreVar, StoreIter, StoreList)

type RSE a = ReaderT Env (StateT Store (ExceptT String IO)) a

data BlockReturn = Ret ELit | NoRet | Yield ELit | Break | Continue
  deriving (Show, Eq)

data BlockRetType = RetType Type | NoRetType | YieldType Type | BreakT | ContinueT
  deriving (Show, Eq)

type GenState = [GenStateElem]

data GenStateElem = GenStateStmt Stmt | ReturnToEnv EnvSt | ForInfo (Type, Loc, GenState, EnvSt, Block)
  deriving (Show)