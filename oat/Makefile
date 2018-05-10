all: Makefile.coq
	$(MAKE) -f $<
	ocaml oat_ast.ml

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	$(RM) Makefile.coq*
	$(RM) oat_ast.ml oat_ast.mli

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@
