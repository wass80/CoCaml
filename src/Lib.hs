module Lib
    ( someFunc
    ) where

import Control.Applicative hiding ((<|>), many)
import Text.Parsec hiding (token)
import Text.Parsec.String
import Text.Parsec.Combinator
import Text.Parsec.Char
import System.IO

someFunc = (+)

{--
test = (
    "若hoge寧ろ無う。" ++
    "取あ則ろ。" ++
    "以再あ為い如う。" ++
    "以あ為い如う。"
  )

someFunc :: IO ()
someFunc = do
  cont <- getContents
--  parseTest pProg cont
  case parse pProg "" cont of
    Right x -> putStrLn $ buildOCaml x
    Left x -> hPrint stderr x

skipSpace :: Parser a -> Parser a
skipSpace p = many space *> p <* many space

ptoken :: Parser String
ptoken =  skipSpace token

alphas :: Parser Char
alphas = oneOf $ ['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z'] ++ "'_()+-="

regchars = "、。也為如若寧無呼取何也以定」"

token :: Parser String
token = many1 alphas <|> (do x <- noneOf regchars; return [x])

pIdt :: Parser Idt
pIdt = liftA Idt $ ptoken

pNext :: Parser Expr
pNext = foldl1 Next <$> (skipSpace pApply `sepBy1` char '、')

pApply :: Parser Expr
pApply = foldl1 Apply <$> many1 (skipSpace pExpr)

pExpr :: Parser Expr
pExpr = skipSpace $ pLet <|> pIf <|> pLString
                 <|> pCall <|> pParen<|> pLIdt <|> pNext

pLIdt = LIdt <$> pIdt

pLString :: Parser Expr
pLString = between (char '「') (char '」')
           (liftA LString $ many $ noneOf "」")

pCall = Call <$> (char '呼' *> pExpr)

pIf = do
  char '若'; c <- pExpr
  char '寧'; t <- pExpr
  char '無'; f <- pExpr
  return $ If c t f

pNonRecLet = do
  char '以'; i <- many1 pIdt
  char '為'; f <- pExpr
  char '如'; e <- pExpr
  return $ Let NonRec i f e

pRecLet = do
  char '以'; char '再'; i <- many1 pIdt
  char '為'; f <- pExpr
  char '如'; e <- pExpr
  return $ Let Rec i f e

pLet = try pRecLet <|> pNonRecLet

pParen = char '何' *> pExpr <* char '也'

pNonRecDef = do
  char '定'; i <- many1 pIdt
  char '為'; e <- pExpr
  return $ Def NonRec i e

pRecDef = do
  char '定'; char '再'; i <- many1 pIdt
  char '為'; e <- pExpr
  return $ Def Rec i e

pDef = try pRecDef <|> pNonRecDef

pSent :: Parser Sent
pSent = pDef <|> (Sent <$> skipSpace pExpr)

pProg :: Parser Prog
pProg = many $ skipSpace pSent <* char '。' <* many space

buildOCaml :: Prog -> String
buildOCaml (h:t) = bSent h ++ ";;\n" ++ buildOCaml t
buildOCaml [] = ";;\n"

bSent :: Sent -> String
bSent (Sent e) = bExpr e
bSent (Def NonRec i e) = "let " ++ bIdts i ++ " = " ++ bExpr e
bSent (Def Rec i e) = "let rec " ++ bIdts i ++ " = " ++ bExpr e

bExpr :: Expr -> String
bExpr (Next a b) = "( " ++ bExpr a ++ " |> " ++ bExpr b ++ " ) "
bExpr (Apply f c) = " ( " ++ bExpr f ++ " " ++ bExpr c ++ " ) "
bExpr (Let NonRec c a b) =
  " (let " ++ bIdts c ++ " = " ++ bExpr a ++ " in " ++ bExpr b ++ " ) "
bExpr (Let Rec c a b) =
  " (let rec " ++ bIdts c ++ " = " ++ bExpr a ++ " in " ++ bExpr b ++ " ) "
bExpr (Fun i e) =
  " (fun " ++ bIdt i ++ " -> " ++ bExpr e ++ " ) "
bExpr (If c a b) = "(if " ++ bExpr c ++ " then " ++ bExpr a ++ " else " ++ bExpr b ++ " )"
bExpr (LIdt c) = bIdt c
bExpr (LString s) = "\"" ++ s ++ "\""
bExpr (Call f) = " ( " ++ bExpr f ++ "()) "
bExpr _ = "ENIL"

bIdts :: [Idt] -> String
bIdts (h:t) = bIdt h ++ " " ++ bIdts t
bIdts [] = ""

bIdt :: Idt -> String
bIdt (Idt c) = c
--}
