
.PHONY: clean view_trace typecheck_c run_c debug_c typecheck repl debug

override CCFLAGS += -Wall -Wextra -fno-strict-aliasing

clean:
	git clean -fdx

view_trace: src/viewer.html build/trace.data.js
	python3 -m http.server 8000 &
	firefox localhost:8000/$<

build/trace.data.js: build/bubs.trace.run
	echo "var frames = [\`digraph {label=\"Data loaded, press buttons to render\"}" > $@
	./$< | sed "s/\/\/ BEGIN DOT DUMP/\`,\`/" >> $@
	echo "" >> $@
	echo "\`]" >> $@

# Launch valgrind in background (bash syntax: &),
#  then launch gdb in foreground, and connect the two
# This relies on only one valgrind session running on the machine
# To ensure this stays true, users can type "monitor v.kill"
# before closing GDB session.
debug_c: build/bubs.debug.run
	valgrind --vgdb-error=0 ./$< & gdb -ex "target remote | vgdb" ./$<

run_c: build/bubs.run
	./$<

typecheck_c: src/bubs.c
	gcc $(CCFLAGS) -fsyntax-only $<

build/bubs.trace.run: src/bubs.c Makefile
	mkdir -p build
	gcc $(CCFLAGS) -DCONFIG_DUMP_DOT_ON_WHNF $< -o $@
	chmod +x $@

build/bubs.debug.run: src/bubs.c Makefile
	mkdir -p build
	gcc $(CCFLAGS) -g $< -o $@
	chmod +x $@

build/bubs.run: src/bubs.c Makefile
	mkdir -p build
	gcc $(CCFLAGS) $< -o $@
	chmod +x $@

typecheck:
	poly --script src/bubs.sml

repl:
	rlwrap poly --use src/bubs.sml

debug:
	rlwrap poly --eval "PolyML.Compiler.debug := true; open PolyML.Debug; use \"src/bubs.sml\";"
