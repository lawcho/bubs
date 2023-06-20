
.PHONY: clean view_trace view_trace_static typecheck_c run_c debug_c typecheck repl debug
.PRECIOUS: build/trace.data.txt

override CCFLAGS += -Wall -Wextra -fno-strict-aliasing -rdynamic -g -ldl -DCONFIG_USE_DLADDR -DCONFIG_ENABLE_LAMBDA_MACRO -DCONFIG_ENABLE_DEBUG_PRINTFLN

clean:
	git clean -fdx

build/trace.packed.dot: build/trace.data.txt
	dot $< | gvpack -n -array_il3 -Gbgcolor=none > $@

build/trace.png: build/trace.packed.dot
	neato -n2 -Tpng < $< > $@

build/trace.svg: build/trace.packed.dot
	neato -n2 -Tsvg < $< > $@

build/trace.pdf: build/trace.packed.dot
	neato -n2 -Tpdf < $< > $@

view_trace: src/viewer.html build/trace.data.js
	firefox $<

build/trace.data.js: build/trace.data.txt
	echo "var frames = [\`digraph {label=\"Data loaded, press buttons to render\"}" > $@
	cat $< | sed "s/\/\/ BEGIN DOT DUMP/\`,\`/" >> $@
	echo "" >> $@
	echo "\`]" >> $@

PLAIN_FIND="Op1T | <parents> | <copy> | op_id| {Op1Arg| { <Op1Arg_pred> | <Op1Arg_child> | <Op1Arg_succ>}}"
PLAIN_REPLACE="{{ (root) | <Op1Arg_pred> | <Op1Arg_child> | <Op1Arg_succ>}}"
# REGEX_FIND=(LamBody|AppFun|AppArg|Op2Arg1|Op2Arg2|Op1Arg)\|
# REGEX_REPLACE=
build/trace.data.txt: build/bubs.trace.run
	./$< | sed \
                -e 's#$(value PLAIN_FIND)#$(value PLAIN_REPLACE)#g' \
                -r -e 's#$(value REGEX_FIND)#$(value REGEX_REPLACE)#g' \
                > $@

test:
	echo $(value FIND)

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
