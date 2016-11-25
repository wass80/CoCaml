module Transpiler where

import Ast
import Data.Char (ord, chr)
import Data.List (intercalate)

uord :: Char -> String
uord c = 'u' : (show $ ord c)

uchr :: String -> Char
uchr ('u' : t) = chr $ read t

idt :: Idt -> String
idt (Idt idt@(s:_))
  | s `elem` alphas = idt
  | otherwise = concatMap uord idt

args :: [Idt] -> String
args = intercalate " " . map idt

rec :: IsRec -> String
rec Rec = " rec"
rec NonRec = ""

expr :: Expr -> String
expr (LIdt i) = idt i
expr (LString i) = "\"" ++ i ++ "\""
expr (Apply f a) = "(" ++ expr f ++ " " ++ expr a ++ ")"
expr (Pipe a b) = "(" ++ expr a ++ " |> " ++ expr b ++ ")"
expr (Let r a b c d) =
  "(let" ++ rec r ++ " " ++ idt a ++ " " ++ args b ++ " = "
  ++ expr c ++ " in " ++ expr d ++ ")"
expr (If c t f) = "(if " ++ expr c ++ " then " ++ expr t ++ " else " ++ expr f ++ " end)"
expr (Call f) = "(" ++ expr f ++ "())"

sent :: Sent -> String
sent (Sent s) = expr s ++ ";;\n"
sent (Def r a b c) =
  "let" ++ rec r ++ " " ++ idt a ++ " " ++ args b ++ " = " ++ expr c ++ ";;\n"

prog :: Prog -> String
prog = concatMap sent

transpile :: Prog -> String
transpile = prog
