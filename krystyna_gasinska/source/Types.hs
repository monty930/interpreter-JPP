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

type EnvIter = M.Map Ident Loc

type StoreIter = M.Map Loc (Type, GenState, EnvVarIter)

type EnvProc = M.Map Ident (RetVal, [Arg], Block, EnvVarIter, Bool)

type EnvGen = M.Map Ident (Type, [Arg], Block, EnvVarIter)

type EnvVarIter = (EnvVar, EnvIter)

type Env = (EnvVarIter, EnvProc, EnvGen)

type Store = (StoreVar, StoreIter)

type RSE a = ReaderT Env (StateT Store (ExceptT String IO)) a

data BlockReturn = Ret ELit | NoRet | Yield ELit | Break | Continue
  deriving (Show, Eq)

data BlockRetType = RetType Type | NoRetType | YieldType Type | BreakT | ContinueT
  deriving (Show, Eq)

type GenState = [GenStateElem]

data GenStateElem = GenStateStmt Stmt | ReturnToEnv EnvVarIter | ForInfo (Type, Loc, GenState, EnvVarIter, Block)
  deriving (Show)