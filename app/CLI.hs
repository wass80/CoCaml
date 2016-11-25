import Parser (parse)
import Transpiler (transpile)

main :: IO ()
main = do
  cont <- getContents
  putStrLn $ case (parse cont) of
    Right ast -> transpile ast
    Left error -> show error
