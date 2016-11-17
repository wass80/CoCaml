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

