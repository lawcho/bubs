
.PHONY: typecheck repl

typecheck:
	poly --script bubs.sml

repl:
	rlwrap poly --use bubs.sml
