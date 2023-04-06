
.PHONY: typecheck repl debug

typecheck:
	poly --script bubs.sml

repl:
	rlwrap poly --use bubs.sml

debug:
	rlwrap poly --eval "PolyML.Compiler.debug := true; open PolyML.Debug; use \"bubs.sml\";"
