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

skipSpace :: Parser a -> Parser a
skipSpace p = many space *> p <* many space

alphas :: Parser Char
alphas = oneOf $ ['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z'] ++ "'_()+-="

regchars :: [Char]
regchars = "　 、。也為如若寧無呼取何也以定「」"

tokenList :: Parser String
tokenList = skipSpace (noneOf regchars) `sepBy` char '-'

token :: Parser String
token = skipSpace $ (many1 alphas <|>  tokenList)

