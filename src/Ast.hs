module Ast where

type Prog = [Sent]

data IsRec = Rec | NonRec deriving (Show, Eq)

data Sent
  = Def IsRec [Idt] Expr
  | Sent Expr
  deriving (Show, Eq)

data Expr
  = Let IsRec Idt [Idt] Expr Expr
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
  | Next Expr
  | Nil
  deriving (Show, Eq)

data Idt = Idt String deriving (Show, Eq)

alphas :: [Char]
alphas = ['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z'] ++ "'_()+-="

regchars :: [Char]
regchars = "　 、。也為如若寧無呼取何也以定「」"
{--

<program> = <sentence>+

<sentence> ::=
  <space>* '定' <space>* '再'? <idt>+ '為' <expr> 。<space>* |
  <expr> 。<space>*

<expr> ::= <pipe>

<pipe> ::= <apply> (、 <apply>)+
<apply> ::= <atom> (<expr>)+
<atom> :: = 
  '以' '再'? <idt>+ '為' <pipe> '如' <pipe> |
  '若' <pipe> '寧' <pipe> '無' <pipe> |
  '字' <pipe> |
  (並 <expr>)+ 空 |
  「 <string> 」|
  <number> |
  呼 <expr> |
  次 <expr> |
  <idt> |
  何 <expr> 也

<idt> ::= <alpha> <char> (- <char>)* | <idt> 之 <idt>

--}
