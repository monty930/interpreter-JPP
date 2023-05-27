-- File generated by the BNF Converter (bnfc 2.9.4.1).

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Pretty-printer for PrintGrammar.

module PrintGrammar where

import Prelude
  ( ($), (.)
  , Bool(..), (==), (<)
  , Int, Integer, Double, (+), (-), (*)
  , String, (++)
  , ShowS, showChar, showString
  , all, elem, foldr, id, map, null, replicate, shows, span
  )
import Data.Char ( Char, isSpace )
import qualified AbsGrammar

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 False (map ($ "") $ d []) ""
  where
  rend
    :: Int        -- ^ Indentation level.
    -> Bool       -- ^ Pending indentation to be output before next character?
    -> [String]
    -> ShowS
  rend i p = \case
      "["      :ts -> char '[' . rend i False ts
      "("      :ts -> char '(' . rend i False ts
      "{"      :ts -> onNewLine i     p . showChar   '{'  . new (i+1) ts
      "}" : ";":ts -> onNewLine (i-1) p . showString "};" . new (i-1) ts
      "}"      :ts -> onNewLine (i-1) p . showChar   '}'  . new (i-1) ts
      [";"]        -> char ';'
      ";"      :ts -> char ';' . new i ts
      t  : ts@(s:_) | closingOrPunctuation s
                   -> pending . showString t . rend i False ts
      t        :ts -> pending . space t      . rend i False ts
      []           -> id
    where
    -- Output character after pending indentation.
    char :: Char -> ShowS
    char c = pending . showChar c

    -- Output pending indentation.
    pending :: ShowS
    pending = if p then indent i else id

  -- Indentation (spaces) for given indentation level.
  indent :: Int -> ShowS
  indent i = replicateS (2*i) (showChar ' ')

  -- Continue rendering in new line with new indentation.
  new :: Int -> [String] -> ShowS
  new j ts = showChar '\n' . rend j True ts

  -- Make sure we are on a fresh line.
  onNewLine :: Int -> Bool -> ShowS
  onNewLine i p = (if p then id else showChar '\n') . indent i

  -- Separate given string from following text by a space (if needed).
  space :: String -> ShowS
  space t s =
    case (all isSpace t', null spc, null rest) of
      (True , _   , True ) -> []              -- remove trailing space
      (False, _   , True ) -> t'              -- remove trailing space
      (False, True, False) -> t' ++ ' ' : s   -- add space if none
      _                    -> t' ++ s
    where
      t'          = showString t []
      (spc, rest) = span isSpace s

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt i = concatD . map (prt i)

instance Print Char where
  prt _ c = doc (showChar '\'' . mkEsc '\'' c . showChar '\'')

instance Print String where
  prt _ = printString

printString :: String -> Doc
printString s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q = \case
  s | s == q -> showChar '\\' . showChar s
  '\\' -> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  s -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print AbsGrammar.Ident where
  prt _ (AbsGrammar.Ident i) = doc $ showString i
instance Print (AbsGrammar.Program' a) where
  prt i = \case
    AbsGrammar.Program_T _ topdefs -> prPrec i 0 (concatD [prt 0 topdefs])

instance Print (AbsGrammar.TopDef' a) where
  prt i = \case
    AbsGrammar.ProcDecl_T _ retval id_ args -> prPrec i 0 (concatD [prt 0 retval, prt 0 id_, doc (showString "("), prt 0 args, doc (showString ")"), doc (showString ";")])
    AbsGrammar.ProcDef_T _ retval id_ args block -> prPrec i 0 (concatD [prt 0 retval, prt 0 id_, doc (showString "("), prt 0 args, doc (showString ")"), prt 0 block])
    AbsGrammar.GlobVar_T _ type_ id_ expr -> prPrec i 0 (concatD [doc (showString "Glob"), prt 0 type_, prt 0 id_, doc (showString "="), prt 0 expr, doc (showString ";")])
    AbsGrammar.Gener_T _ type_ id_ args block -> prPrec i 0 (concatD [doc (showString "Gen"), prt 0 type_, prt 0 id_, doc (showString "("), prt 0 args, doc (showString ")"), prt 0 block])

instance Print [AbsGrammar.TopDef' a] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print (AbsGrammar.Arg' a) where
  prt i = \case
    AbsGrammar.Arg_T _ type_ id_ -> prPrec i 0 (concatD [prt 0 type_, prt 0 id_])
    AbsGrammar.ArgList_T _ id_ -> prPrec i 0 (concatD [doc (showString "list"), prt 0 id_])

instance Print [AbsGrammar.Arg' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print (AbsGrammar.Block' a) where
  prt i = \case
    AbsGrammar.Block_T _ stmts -> prPrec i 0 (concatD [doc (showString "{"), prt 0 stmts, doc (showString "}")])

instance Print [AbsGrammar.Stmt' a] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print (AbsGrammar.Stmt' a) where
  prt i = \case
    AbsGrammar.Empty_T _ -> prPrec i 0 (concatD [doc (showString ";")])
    AbsGrammar.BStmt_T _ block -> prPrec i 0 (concatD [prt 0 block])
    AbsGrammar.Decl_T _ type_ id_ expr -> prPrec i 0 (concatD [prt 0 type_, prt 0 id_, doc (showString "="), prt 0 expr, doc (showString ";")])
    AbsGrammar.Ass_T _ id_ expr -> prPrec i 0 (concatD [prt 0 id_, doc (showString "="), prt 0 expr, doc (showString ";")])
    AbsGrammar.Incr_T _ id_ -> prPrec i 0 (concatD [prt 0 id_, doc (showString "++"), doc (showString ";")])
    AbsGrammar.Decr_T _ id_ -> prPrec i 0 (concatD [prt 0 id_, doc (showString "--"), doc (showString ";")])
    AbsGrammar.Break_T _ -> prPrec i 0 (concatD [doc (showString "break"), doc (showString ";")])
    AbsGrammar.Continue_T _ -> prPrec i 0 (concatD [doc (showString "continue"), doc (showString ";")])
    AbsGrammar.Cond_T _ expr block -> prPrec i 0 (concatD [doc (showString "if"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 block])
    AbsGrammar.CondElse_T _ expr block1 block2 -> prPrec i 0 (concatD [doc (showString "if"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 block1, doc (showString "else"), prt 0 block2])
    AbsGrammar.While_T _ expr block -> prPrec i 0 (concatD [doc (showString "while"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 block])
    AbsGrammar.Return_T _ expr -> prPrec i 0 (concatD [doc (showString "return"), doc (showString "("), prt 0 expr, doc (showString ")")])
    AbsGrammar.Yield_T _ expr -> prPrec i 0 (concatD [doc (showString "yield"), doc (showString "("), prt 0 expr, doc (showString ")")])
    AbsGrammar.DeclGen_T _ id_1 id_2 funargs -> prPrec i 0 (concatD [doc (showString "gen"), prt 0 id_1, doc (showString "="), prt 0 id_2, doc (showString "("), prt 0 funargs, doc (showString ")"), doc (showString ";")])
    AbsGrammar.ForGen_T _ id_1 id_2 funargs block -> prPrec i 0 (concatD [doc (showString "for"), doc (showString "("), prt 0 id_1, doc (showString "in"), prt 0 id_2, doc (showString "("), prt 0 funargs, doc (showString ")"), doc (showString ")"), prt 0 block])
    AbsGrammar.DeclList_T _ id_ exprs -> prPrec i 0 (concatD [doc (showString "list"), prt 0 id_, doc (showString "="), doc (showString "["), prt 0 exprs, doc (showString "]"), doc (showString ";")])
    AbsGrammar.PushToList_T _ id_ expr -> prPrec i 0 (concatD [prt 0 id_, doc (showString ".push"), doc (showString "("), prt 0 expr, doc (showString ")"), doc (showString ";")])
    AbsGrammar.PopFromList_T _ id_ -> prPrec i 0 (concatD [prt 0 id_, doc (showString ".pop"), doc (showString ";")])
    AbsGrammar.AddToList_T _ id_ expr1 expr2 -> prPrec i 0 (concatD [prt 0 id_, doc (showString ".add"), doc (showString "("), prt 0 expr1, doc (showString ").("), prt 0 expr2, doc (showString ")"), doc (showString ";")])
    AbsGrammar.RemoveFromList_T _ id_ expr -> prPrec i 0 (concatD [prt 0 id_, doc (showString ".remove"), doc (showString "("), prt 0 expr, doc (showString ")"), doc (showString ";")])
    AbsGrammar.SExp_T _ expr -> prPrec i 0 (concatD [prt 0 expr, doc (showString ";")])

instance Print (AbsGrammar.Type' a) where
  prt i = \case
    AbsGrammar.Int_T _ -> prPrec i 0 (concatD [doc (showString "int")])
    AbsGrammar.CharT_T _ -> prPrec i 0 (concatD [doc (showString "char")])
    AbsGrammar.Str_T _ -> prPrec i 0 (concatD [doc (showString "string")])
    AbsGrammar.Bool_T _ -> prPrec i 0 (concatD [doc (showString "bool")])

instance Print (AbsGrammar.RetVal' a) where
  prt i = \case
    AbsGrammar.FunRetVal_T _ type_ -> prPrec i 0 (concatD [prt 0 type_])
    AbsGrammar.FunRetVoid_T _ -> prPrec i 0 (concatD [doc (showString "Proc")])

instance Print (AbsGrammar.Var' a) where
  prt i = \case
    AbsGrammar.Var_T _ id_ -> prPrec i 0 (concatD [prt 0 id_])

instance Print (AbsGrammar.Expr' a) where
  prt i = \case
    AbsGrammar.EListElem_T _ id_ expr -> prPrec i 7 (concatD [prt 0 id_, doc (showString "["), prt 0 expr, doc (showString "]")])
    AbsGrammar.EVar_T _ var -> prPrec i 7 (concatD [prt 0 var])
    AbsGrammar.ELit_T _ elit -> prPrec i 7 (concatD [prt 0 elit])
    AbsGrammar.App_T _ id_ funargs -> prPrec i 7 (concatD [prt 0 id_, doc (showString "("), prt 0 funargs, doc (showString ")")])
    AbsGrammar.Neg_T _ expr -> prPrec i 6 (concatD [doc (showString "-"), prt 7 expr])
    AbsGrammar.Not_T _ expr -> prPrec i 6 (concatD [doc (showString "!"), prt 7 expr])
    AbsGrammar.EMul_T _ expr1 mulop expr2 -> prPrec i 5 (concatD [prt 5 expr1, prt 0 mulop, prt 6 expr2])
    AbsGrammar.EAdd_T _ expr1 addop expr2 -> prPrec i 4 (concatD [prt 4 expr1, prt 0 addop, prt 5 expr2])
    AbsGrammar.ERel_T _ expr1 relop expr2 -> prPrec i 3 (concatD [prt 3 expr1, prt 0 relop, prt 4 expr2])
    AbsGrammar.EAnd_T _ expr1 expr2 -> prPrec i 2 (concatD [prt 3 expr1, doc (showString "&&"), prt 2 expr2])
    AbsGrammar.EOr_T _ expr1 expr2 -> prPrec i 1 (concatD [prt 2 expr1, doc (showString "||"), prt 1 expr2])
    AbsGrammar.ECast_T _ type_ expr -> prPrec i 6 (concatD [doc (showString "("), prt 0 type_, doc (showString ")"), prt 6 expr])
    AbsGrammar.EGenNext_T _ id_ -> prPrec i 6 (concatD [doc (showString "next"), doc (showString "("), prt 0 id_, doc (showString ")")])

instance Print (AbsGrammar.ELit' a) where
  prt i = \case
    AbsGrammar.ELitInt_T _ n -> prPrec i 0 (concatD [prt 0 n])
    AbsGrammar.ELitBool_T _ ebool -> prPrec i 0 (concatD [prt 0 ebool])
    AbsGrammar.EString_T _ str -> prPrec i 0 (concatD [printString str])
    AbsGrammar.EChar_T _ c -> prPrec i 0 (concatD [prt 0 c])

instance Print (AbsGrammar.EBool' a) where
  prt i = \case
    AbsGrammar.ELitTrue_T _ -> prPrec i 0 (concatD [doc (showString "true")])
    AbsGrammar.ELitFalse_T _ -> prPrec i 0 (concatD [doc (showString "false")])

instance Print (AbsGrammar.FunArg' a) where
  prt i = \case
    AbsGrammar.AsValue_T _ expr -> prPrec i 0 (concatD [prt 0 expr])
    AbsGrammar.AsRef_T _ var -> prPrec i 0 (concatD [doc (showString "&"), prt 0 var])

instance Print [AbsGrammar.FunArg' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [AbsGrammar.Expr' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print (AbsGrammar.AddOp' a) where
  prt i = \case
    AbsGrammar.Plus_T _ -> prPrec i 0 (concatD [doc (showString "+")])
    AbsGrammar.Minus_T _ -> prPrec i 0 (concatD [doc (showString "-")])

instance Print (AbsGrammar.MulOp' a) where
  prt i = \case
    AbsGrammar.Times_T _ -> prPrec i 0 (concatD [doc (showString "*")])
    AbsGrammar.Div_T _ -> prPrec i 0 (concatD [doc (showString "/")])
    AbsGrammar.Mod_T _ -> prPrec i 0 (concatD [doc (showString "%")])

instance Print (AbsGrammar.RelOp' a) where
  prt i = \case
    AbsGrammar.LTH_T _ -> prPrec i 0 (concatD [doc (showString "<")])
    AbsGrammar.LE_T _ -> prPrec i 0 (concatD [doc (showString "<=")])
    AbsGrammar.GTH_T _ -> prPrec i 0 (concatD [doc (showString ">")])
    AbsGrammar.GE_T _ -> prPrec i 0 (concatD [doc (showString ">=")])
    AbsGrammar.EQU_T _ -> prPrec i 0 (concatD [doc (showString "==")])
    AbsGrammar.NE_T _ -> prPrec i 0 (concatD [doc (showString "!=")])
