module LibSpec (main, spec) where

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

import Lib

main :: IO ()
main = hspec spec

spec = do
  describe "ok" $ do
    prop "test" $ (\a b -> someFunc a b == a + b)

