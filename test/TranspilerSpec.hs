module TranspilerSpec (main, spec) where

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

import Ast
import Transpiler

main :: IO ()
main = hspec spec

testTrans f e a = it e (f a == e)
testExpr = testTrans expr

i :: String -> Expr
i = LIdt . Idt

spec = do
  describe "apply" $ do
    testExpr "((a b) c)" (Apply (Apply (i "a") (i "b")) (i "c"))
  describe "pipe" $ do
    testExpr "(a |> (f b))"
      (Pipe (LIdt $ Idt "a") (Apply (LIdt $ Idt "f") (LIdt $ Idt "b")))
  describe "lidt" $ do
    testExpr "u25991" (i "文")
    testExpr "u25991u23383" (i "文字")
    testExpr "aiu" (i "aiu")
  describe "lstring" $ do
    testExpr "\"文字\"" (LString "文字")
  describe "llet" $ do
    testExpr "(let a b = c in d)"
      (Let NonRec (Idt "a") [Idt "b"] (i "c") (i "d"))
    testExpr "(let rec a b c = (c d) in (e |> f))"
      (Let Rec (Idt "a") [Idt "b", Idt "c"]
        (Apply (i "c") (i "d")) (Pipe (i "e") (i "f")))
  describe "lif" $ do
    testExpr "(if a then (b |> c) else d end)"
      (If (i "a") (Pipe (i "b") (i "c")) (i "d"))
  describe "sent" $ do
    testTrans sent "(a b);;\n" (Sent (Apply (i "a") (i "b")))
  describe "def" $ do
    testTrans sent "let rec x y = (a b);;\n"
      (Def Rec (Idt "x") [Idt "y"] (Apply (i "a") (i "b")))
  describe "prog" $ do
    testTrans prog "(a b);;\na;;\n"
      [Sent (Apply (i "a") (i "b")), Sent (i "a")]
