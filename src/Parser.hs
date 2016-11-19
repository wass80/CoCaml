module Parser where

import Ast

import Control.Applicative hiding ((<|>), many)
import Text.Parsec hiding (token)
import Text.Parsec.String
import Text.Parsec.Combinator
import Text.Parsec.Char

parse :: String -> Either ParseError Prog
parse program = Text.Parsec.parse prog "" program

prog :: Parser Ast.Prog
prog = return []

alphas :: Parser Char
alphas = oneOf $ ['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z'] ++ "'_()+-="

regchars :: [Char]
regchars = "　 、。也為如若寧無呼取何也以定「」"

tokenList :: Parser String
tokenList = (spaces *> noneOf regchars <* spaces )`sepBy1` char '-'

token :: Parser String
token = spaces *>  (many1 alphas <|> tokenList) <* spaces

idt :: Parser Idt
idt = Idt <$> token

lidt :: Parser Expr
lidt = LIdt <$> idt

apply :: Parser Expr
apply = foldl1 Apply <$> many1 expr

pipe :: Parser Expr
pipe = foldl1 Pipe <$> apply `sepBy1` char '、'

expr :: Parser Expr
expr = lidt
