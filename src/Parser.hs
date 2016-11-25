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
tokenList = (many space *> noneOf regchars <* many space )`sepBy1` char '-'

token :: Parser String
token = many space *>  (many1 (oneOf alphas) <|> tokenList) <* many space

idt :: Parser Idt
idt = Idt <$> token

lidt :: Parser Expr
lidt = LIdt <$> idt

lstring :: Parser Expr
lstring = LString <$> (char '「' *> many (noneOf "」") <* char '」')

lparen :: Parser Expr
lparen = char '所' *> expr <* char '也'

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

lif :: Parser Expr
lif = do
  char '若'
  cond <- pipe
  char '寧'
  t <- pipe
  char '無'
  f <- pipe
  return $ If cond t f

call :: Parser Expr
call = do
  char '呼'
  f <- atom
  return $ Call f

atom :: Parser Expr
atom = try $ many space *>
  (call <|> lstring <|> llet <|> lif <|> lparen <|> lidt)

apply :: Parser Expr
apply = foldl1 Apply <$> many atom

pipe :: Parser Expr
pipe = foldl1 Pipe <$> (apply `sepBy1` char '、')

expr :: Parser Expr
expr = pipe <* many space

sent :: Parser Sent
sent = Sent <$> (try $ expr <* many space <*  char '。')

def :: Parser Sent
def = try $ do
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
prog = many (sent <|> def) <* many space <* eof
