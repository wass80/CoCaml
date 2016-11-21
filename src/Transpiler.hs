module Transpiler where

import Ast
import Data.Char (ord)

uord :: Char -> String
uord c = 'u' : (show $ ord c)

transExpr :: Expr -> String
transExpr (LIdt (Idt idt@(s:_)))
  | s `elem` alphas = idt
  | otherwise = concatMap uord idt
