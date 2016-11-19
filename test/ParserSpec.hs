module ParserSpec (main, spec) where

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

import Parser
import Ast

import qualified Text.Parsec as Parsec
import Text.Parsec.String (Parser)

main :: IO ()
main = hspec spec

ptest :: Eq a => Parser a -> String -> a -> Bool
ptest p s x = case (Parsec.parse p "" s) of
  Left _ -> False
  Right ast -> ast == x

testParser p s x = it s $ ptest p s x

spec = do
  describe "parser" $ do
    it "empty" $ parse "" == Right []
  describe "prog" $ do
    it "empty" $ ptest prog "" []
  describe "token" $ do
    testParser token " aaa亜 " "aaa"
    testParser token " 文字 " "文"
    testParser token " 文 - 字 " "文字"
    testParser token " 文-字 - 列 " "文字列"
  describe "idt" $ do
    testParser idt " 文字 " (Idt "文")
  describe "lidt" $ do
    testParser lidt " 文字 " (LIdt $ Idt "文")
  describe "apply" $ do
    testParser apply " 文 " (LIdt $ Idt "文")
    testParser apply " 文字 "
      (Apply (LIdt $ Idt "文") (LIdt $ Idt "字"))
  describe "pipe" $ do
    testParser pipe " 文、字 "
      (Pipe (LIdt $ Idt "文") (LIdt $ Idt "字"))
    testParser pipe " a 、f b "
      (Pipe (LIdt $ Idt "a") (Apply (LIdt $ Idt "f") (LIdt $ Idt "b")))
