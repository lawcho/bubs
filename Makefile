
.PHONY: clean view_trace view_trace_static typecheck_c run_c debug_c typecheck repl debug
.PRECIOUS: build/trace.data.txt

override CCFLAGS += -Wall -Wextra -fno-strict-aliasing -rdynamic -g -ldl -DCONFIG_USE_DLADDR -DCONFIG_ENABLE_LAMBDA_MACRO -DCONFIG_ENABLE_DEBUG_PRINTFLN

clean:
	git clean -fdx

build/trace.png: build/trace.data.txt
	dot $< | gvpack -array -Glabel="" | neato -s -n2 -Tpng > $@

view_trace: src/viewer.html build/trace.data.js
	firefox $<

build/trace.data.js: build/trace.data.txt
	echo "var frames = [\`digraph {label=\"Data loaded, press buttons to render\"}" > $@
	cat $< | sed "s/\/\/ BEGIN DOT DUMP/\`,\`/" >> $@
	echo "" >> $@
	echo "\`]" >> $@

build/trace.data.txt: build/bubs.trace.run
	./$< > $@

# Launch valgrind in background (bash syntax: &),
#  then launch gdb in foreground, and connect the two
# This relies on only one valgrind session running on the machine
# To ensure this stays true, users can type "monitor v.kill"
# before closing GDB session.
debug_c: build/bubs.debug.run
	valgrind --vgdb-error=0 ./$< & gdb -ex "target remote | vgdb" ./$<

run_c: build/bubs.run
	./$<

C_SOURCES = src/tests.c src/bubs.h src/bubs.c

typecheck_c: $(C_SOURCES)
	gcc $(CCFLAGS) -fsyntax-only $^

build/bubs.trace.run: $(C_SOURCES)
	mkdir -p build
	gcc $(CCFLAGS) -DCONFIG_DUMP_DOT_ON_WHNF -DCONFIG_DUMP_DOT_IN_REDUCTION $^ -o $@
	chmod +x $@

build/bubs.debug.run: $(C_SOURCES)
	mkdir -p build
	gcc $(CCFLAGS) -g $^ -o $@
	chmod +x $@

build/bubs.run: $(C_SOURCES)
	mkdir -p build
	gcc $(CCFLAGS) $^ -o $@
	chmod +x $@

typecheck:
	poly --script src/bubs.sml

repl:
	rlwrap poly --use src/bubs.sml

debug:
	rlwrap poly --eval "PolyML.Compiler.debug := true; open PolyML.Debug; use \"src/bubs.sml\";"
