all: test_serialization
test_serialization: test_serialization.ml
	OCAMLPATH="../meta" ocamlfind ocamlc -linkpkg -package hbugs-common -o test_serialization test_serialization.ml
clean:
	rm -f *.cm[io] test_serialization
