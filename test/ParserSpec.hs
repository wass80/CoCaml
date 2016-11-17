module ParserSpec (main, spec) where

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

import Parser

main :: IO ()
main = hspec spec

spec = do
  describe "parser" $ do
    prop "empty" $ parse "" == Right []
