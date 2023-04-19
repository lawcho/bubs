
.PHONY: typecheck_c run_c debug_c typecheck repl debug

override CCFLAGS += -Wall -Wextra -fno-strict-aliasing

# Launch valgrind in background (bash syntax: &),
#  then launch gdb in foreground, and connect the two
# This relies on only one valgrind session running on the machine
# To ensure this stays true, users can type "monitor v.kill"
# before closing GDB session.
debug_c: bubs.debug.run
	valgrind --vgdb-error=0 ./$< & gdb -ex "target remote | vgdb" ./$<

run_c: bubs.run
	./$<

typecheck_c: bubs.c
	gcc $(CCFLAGS) -fsyntax-only $<

bubs.debug.run: bubs.c Makefile
	gcc $(CCFLAGS) -g $< -o $@
	chmod +x $@

bubs.run: bubs.c Makefile
	gcc $(CCFLAGS) $< -o $@
	chmod +x $@

typecheck:
	poly --script bubs.sml

repl:
	rlwrap poly --use bubs.sml

debug:
	rlwrap poly --eval "PolyML.Compiler.debug := true; open PolyML.Debug; use \"bubs.sml\";"
