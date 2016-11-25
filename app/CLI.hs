import System.Environment
import System.IO

import Parser (parse)
import Transpiler (transpile)

main :: IO ()
main = do
  args <- getArgs
  cont <- case args of
    (h:_) -> readFile h
    [] -> getContents
  putStrLn $ case (parse cont) of
    Right ast -> transpile ast
    Left error -> show error
