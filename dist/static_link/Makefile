all: static_link
static_link: static_link.ml
	ocamlfind ocamlc -package unix,str -linkpkg -o $@ $<
clean:
	rm -f static_link.cm* static_link
