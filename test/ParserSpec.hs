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

i :: String -> Expr
i = LIdt . Idt

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
  describe "apply" $ do
    testParser apply " 文 " (i "文")
    testParser apply " f a b "
      (Apply (Apply (i "f") (i "a")) (i "b"))
  describe "pipe" $ do
    testParser pipe " a、b 、c "
      (Pipe (Pipe (i "a") (i "b")) (i "c"))
    testParser pipe " a 、f b "
      (Pipe (i "a") (Apply (i "f") (i "b")))
  describe "lidt" $ do
    testParser lidt " 文字 " (i "文")
  describe "llet" $ do
    testParser llet "以 a b 為 c 如 d"
      (Let NonRec (Idt "a") [Idt "b"] (i "c") (i "d"))
    testParser llet "以再 a b 為 c d 如 e、f"
      (Let Rec (Idt "a") [Idt "b"]
        (Apply (i "c") (i "d")) (Pipe (i "e") (i "f")))
  describe "lif" $ do
    testParser lif "若あ寧 b、c 無 d "
      (If (i "あ") (Pipe (i "b") (i "c")) (i "d"))
  describe "sent" $ do
    testParser sent "a b。" (Sent (Apply (i "a") (i "b")))
  describe "def" $ do
    testParser def " 定 a b c 為 d、e。"
      (Def NonRec (Idt "a") [Idt "b", Idt "c"] (Pipe (i "d") (i "e")))
    testParser def " 定 再 a b c 為 d、e。"
      (Def Rec (Idt "a") [Idt "b", Idt "c"] (Pipe (i "d") (i "e")))
  describe "prog" $ do
    testParser prog "a b。あ。"
      [Sent (Apply (i "a") (i "b")), Sent (i "あ")]
    testParser prog "a b。   "
      [Sent (Apply (i "a") (i "b"))]
    testParser prog " a b。  定 a b 為 c。 "
      [Sent (Apply (i "a") (i "b")),
       Def NonRec (Idt "a") [Idt "b"] (i "c")]
