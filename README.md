# 孔Caml

[Demo](https://wass80.github.io/CoCaml/demo/)

漢文ベース関数型プログラミング言語です。
OCamlの構文です。

# Interpreter

(TODO)

# Compiler

```
$ less demo/demo.ml
定曰為print_string。
定名為string_of_int。
定加為(+)。
定減為(-)。
定等為(==)。
定零為0。
定一為1。
定改-行為print_newline。
定読為read_line。
定読-数為read_int。

曰「にーはお、世界」。呼改-行。
定再 階-加 数 為
  若 等数零
    寧 零
    無 加数 所 減数一、階-加 也。
呼読-数、階-加、名、曰。呼改-行。

$ ocamlopt -pp "stack exec cocaml" demo/demo.ml
$ ./a.out
にーはお、世界
10
55
```

# Syntax

[AST + BNF](./src/Ast.hs)

# Requirements

* Haskell
* OCaml
* Parsec
* Haste

# License

MIT
