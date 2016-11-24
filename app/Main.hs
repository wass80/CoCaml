module Main where


import Haste
import Haste.DOM
import Haste.Events

import Parser (parse)
import Transpiler (transpile)

main :: IO ()
main = do
    -- elemById ::  MonadIO m => ElemID -> m (Maybe Elem)
    Just input <- elemById "calcInput"
    Just ast <- elemById "ast"
    Just output <- elemById "output"
    -- onEvent element event (EventData evt -> m ()) という形
    -- この場合 e にはイベント情報が入り，（今回は使っていないが）函数に渡される
    onEvent input KeyUp $ \ e -> do
        -- getValue :: (IsElem e, MonadIO m, JSType a) => e -> m (Maybe a)
        Just ln <- getValue input
        case parse ln of
             Right s -> do
               setProp ast "textContent" (show s)
               setProp output "textContent" (transpile s)
             Left l -> do
               setProp ast "textContent" (show l)
               setProp output "textContent" "Error"
    return ()
