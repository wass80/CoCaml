module Parser where

import Ast

import Control.Applicative hiding ((<|>), many)
import Text.Parsec hiding (token)
import Text.Parsec.String
import Text.Parsec.Combinator
import Text.Parsec.Char

parse :: String -> Either ParseError Prog
parse program = Text.Parsec.parse prog "" program

tokenList :: Parser String
tokenList = (spaces *> noneOf regchars <* spaces )`sepBy1` char '-'

token :: Parser String
token = spaces *>  (many1 (oneOf alphas) <|> tokenList) <* spaces

idt :: Parser Idt
idt = Idt <$> token

lidt :: Parser Expr
lidt = LIdt <$> idt

rec :: Parser IsRec
rec = option NonRec $ (try (many space *> char '再') *> return Rec)

llet :: Parser Expr
llet = do
  char '以'
  r <- rec
  f <- idt
  args <- many idt
  char '為'
  val <- pipe
  char '如'
  e <- pipe
  return $ Let r f args val e

atom :: Parser Expr
atom = llet <|> lidt

apply :: Parser Expr
apply = foldl1 Apply <$> many atom

pipe :: Parser Expr
pipe = foldl1 Pipe <$> apply `sepBy1` char '、'

expr :: Parser Expr
expr = pipe

sent :: Parser Sent
sent = Sent <$> expr <* spaces <*  char '。'

def :: Parser Sent
def = do
  many space
  char '定'
  r <- rec
  f <- idt
  args <- many idt
  many space
  char '為'
  val <- pipe
  many space
  char '。'
  return $ Def r f args val

prog :: Parser Prog
prog = many (try sent <|> try def) <* spaces
