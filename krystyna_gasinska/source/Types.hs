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

type EnvProc = M.Map Ident (RetVal, [Arg], Block, EnvVar)

type Env = (EnvVar, EnvProc)

type RSE a = ReaderT Env (StateT StoreVar (ExceptT String IO)) a

data BlockReturn = Ret ELit | NoRet
  deriving (Show)