SOFTWARE=comp

all: $(SOFTWARE)

type.cmi type.cmo: type.ml
	ocamlc -c type.ml

codeGenerator.cmi: type.cmi codeGenerator.mli
	ocamlc -c codeGenerator.mli

coqGenerator.cmi coqGenerator.cmo: type.cmi codeGenerator.cmi coqGenerator.ml
	ocamlc -c coqGenerator.ml

main.cmi main.cmo: type.cmi coqGenerator.cmi main.ml
	ocamlc -c -I +camlp5 camlp5.cma -pp "camlp5o -I `camlp5 -where` pa_o.cmo pa_extend.cmo" main.ml

$(SOFTWARE): type.cmo coqGenerator.cmo main.cmo
	ocamlc -I +camlp5 camlp5.cma -o $(SOFTWARE) type.cmo coqGenerator.cmo main.cmo

clean:
	rm -f *.cmi *.cmo

clear:
	rm -f *.cmi *.cmo $(SOFTWARE)
