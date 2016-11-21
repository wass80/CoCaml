module TranspilerSpec (main, spec) where

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

import Ast
import Transpiler

main :: IO ()
main = hspec spec

testExpr e a = it e (transExpr a == e)

i :: String -> Expr
i s = LIdt $ Idt s

spec =
  describe "idt" $ do
    testExpr "u25991" (i "文")
    testExpr "u25991u23383" (i "文字")
    testExpr "aiu" (i "aiu")

{--
  describe "apply" $ do
    testExp (Apply (i "文"))  "文"
    testParser (Apply (i "文") (Apply (i "字") (i "列"))
      (Apply (LIdt $ Idt "文") (LIdt $ Idt "字"))
  describe "pipe" $ do
    testParser pipe " 文、字 "
      (Pipe (LIdt $ Idt "文") (LIdt $ Idt "字"))
    testParser pipe " a 、f b "
      (Pipe (LIdt $ Idt "a") (Apply (LIdt $ Idt "f") (LIdt $ Idt "b")))
  describe "lidt" $ do
    testParser lidt " 文字 " (LIdt $ Idt "文")
  describe "llet" $ do
    testParser llet "以 a b 為 c 如 d"
      (Let NonRec (Idt "a") [Idt "b"] (i "c") (i "d"))
    testParser llet "以再 a b 為 c d 如 e、f"
      (Let Rec (Idt "a") [Idt "b"]
        (Apply (i "c") (i "d")) (Pipe (i "e") (i "f")))
  describe "sent" $ do
    testParser sent "a b。" (Sent (Apply (i "a") (i "b")))
  describe "prog" $ do
    testParser prog "a b。あ。"
      [Sent (Apply (i "a") (i "b")), Sent (i "あ")]
      --}
