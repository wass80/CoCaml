module Transpiler where

import Ast
import Data.Char (ord)
import Data.List (intercalate)

uord :: Char -> String
uord c = 'u' : (show $ ord c)

idt :: Idt -> String
idt (Idt idt@(s:_))
  | s `elem` alphas = idt
  | otherwise = concatMap uord idt

args :: [Idt] -> String
args = intercalate " " . map idt

expr :: Expr -> String
expr (LIdt i) = idt i
expr (Apply f a) = "(" ++ expr f ++ " " ++ expr a ++ ")"
expr (Pipe a b) = "(" ++ expr a ++ " |> " ++ expr b ++ ")"
expr (Let Rec a b c d) =
  "(let rec " ++ idt a ++ " " ++ args b ++ " = " ++ expr c ++ " in " ++ expr d ++ ")"
expr (Let NonRec a b c d) =
      "(let " ++ idt a ++ " " ++ args b ++ " = " ++ expr c ++ " in " ++ expr d ++ ")"

sent :: Sent -> String
sent (Sent s) = expr s ++ ";;\n"

prog :: Prog -> String
prog = concatMap sent
