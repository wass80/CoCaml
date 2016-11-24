module Main where

import Haste
import Haste.DOM
import Haste.Events
import Haste.Foreign
import Haste.Prim (toJSStr)

import Parser (parse)
import Transpiler (transpile)

setText :: Elem -> String -> IO ()
setText p = setProp p "textContent"

update :: Elem -> Elem -> Elem -> Elem -> IO ()
update input preview ast output = do
  -- getValue :: (IsElem e, MonadIO m, JSType a) => e -> m (Maybe a)
  (Just ln) <- getValue input
  setText preview ln
  case parse ln of
    Right s -> do
      setText ast (show s)
      setText output (transpile s)
    Left l -> do
      setText ast (show l)
      setText output "Error"

main :: IO ()
main = do
  -- elemById ::  MonadIO m => ElemID -> m (Maybe Elem)
  Just input <- elemById "input"
  Just preview <- elemById "preview"
  Just ast <- elemById "ast"
  Just output <- elemById "output"
  update input preview ast output
  -- onEvent element event (EventData evt -> m ()) という形
  -- この場合 e にはイベント情報が入り，（今回は使っていないが）函数に渡される
  onEvent input KeyDown $ \ e -> update input preview ast output
  return ()
