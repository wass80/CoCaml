module ParserSpec (main, spec) where

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

import Parser

import qualified Text.Parsec as Parsec
import Text.Parsec.String (Parser)

main :: IO ()
main = hspec spec

ptest :: Eq a => Parser a -> String -> a -> Bool
ptest p s x = case (Parsec.parse p "" s) of
  Left _ -> False
  Right ast -> ast == x

spec = do
  describe "parser" $ do
    prop "empty" $ parse "" == Right []
  describe "prog" $ do
    prop "empty" $ ptest prog "" []
  describe "token" $ do
    prop "alpha" $ ptest token " aaa亜 " "aaa"
    prop "文字" $ ptest token " 文字 " "文"
    prop "文 - 字" $ ptest token " 文 - 字 " "文字"
    prop "文-字 - 列 " $ ptest token " 文-字 - 列 " "文字列"
