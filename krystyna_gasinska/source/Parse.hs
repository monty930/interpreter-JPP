module Parse where

import AbsGrammar
import LexGrammar   ( Token, mkPosToken )
import ParGrammar   ( pProgram, myLexer )
import PrintGrammar ( Print, printTree )
import SkelGrammar

type ParseFun a = [Token] -> Err a

getParsedProgramFromFile :: ParseFun Program -> FilePath -> IO Program
getParsedProgramFromFile p f = readFile f >>= getParsedProgram p

getParsedProgram :: ParseFun Program -> String -> IO Program
getParsedProgram p s =
  case p ts of
    Left err -> errorWithoutStackTrace err
    Right tree -> return tree
  where
  ts = myLexer s