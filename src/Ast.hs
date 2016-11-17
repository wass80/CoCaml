module Ast where

type Prog = [Sent]

data IsRec = Rec | NonRec deriving (Show, Eq)

data Sent
  = Def IsRec [Idt] Expr
  | Sent Expr
  deriving (Show, Eq)

data Expr
  = Let IsRec [Idt] Expr Expr
  | Fun Idt Expr
  | If Expr Expr Expr
  | LChar Char
  | LString String
  | LList [Expr]
  | LIdt Idt
  | Pipe Expr Expr
  | Apply Expr Expr
  | Number Integer
  | Call Expr
  | Nil
  deriving (Show, Eq)

data Idt = Idt String
  deriving (Show, Eq)

{--

<program> = <sentence>+

<sentence> ::=
  <space>* '定' <space>* '再'? <idt>+ '為' <expr> 。<space>* |
  <expr> 。<space>*

<expr> ::= <space>* <expr'> <space>*
<expr'> ::=
  '以' '再'? <idt>+ '為' <expr> '如' <expr> |
  '若' <expr> '寧' <expr> '無' <expr> |
  '字' <char> |
  (並 <expr>)+ 空 |
  「 <string> 」|
  <number> |
  呼 <expr> |
  何 <expr> 也 |
  <idt> |
  <pipe>

<pipe> =  <apply> (、 <apply>)+
<apply> =  <expr> (<expr>)+

<idt> ::= <alpha> <char> (- <char>)* | <idt> 之 <idt>

--}
