%.o: %.ml
	ocamlfind ocamlopt -package m17n -syntax utf8 $< -o $@
%.ml: %.kanbun
	stack exec kanbun < $< > $@
