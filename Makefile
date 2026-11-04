DC ?= ldc2
LAKE ?= lake
UTIL_PARENT ?= deps
DFLAGS ?= -O -boundscheck=on
MODULES := $(wildcard *.d)
GENERATED_D := generated/rules.d
GENERATED_LEAN := lean/QSym/Generated.lean
IMPORTS := -I.. -I$(UTIL_PARENT)

.PHONY: all generate test demo verify bench bench-certificates clean
all: build/qsym

build generated:
	mkdir -p $@

build/rulec: tools/rulec.d $(MODULES) | build
	$(DC) $(DFLAGS) $(IMPORTS) -i tools/rulec.d -of=$@

generate: build/rulec | generated
	./build/rulec rules/core.qs $(GENERATED_D) $(GENERATED_LEAN)

build/qsym: generate tools/main.d tools/repl.d tools/lineedit.d tools/edit.d tools/unicode.d $(MODULES)
	$(DC) $(DFLAGS) $(IMPORTS) -i tools/main.d -of=$@

test: build/qsym
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/all.d -of=build/tests
	./build/tests
	./build/rulec tests/syntax.qs build/syntax.d build/Syntax.lean
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/generated.d build/syntax.d -of=build/syntax-tests
	./build/syntax-tests
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/scalar.d -of=build/scalar-tests
	./build/scalar-tests --DRT-testmode=run-main build/scalar
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/language.d -of=build/language-tests
	./build/language-tests --DRT-testmode=run-main build/language
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/elementary.d -of=build/elementary-tests
	./build/elementary-tests --DRT-testmode=run-main build/elementary
	python3 tests/repl.py
	python3 tests/terminal.py

demo: build/qsym
	./build/qsym demo

bench: build/qsym
	./build/qsym bench 50000

build/scalar-export: generate tests/scalar.d $(MODULES)
	$(DC) $(DFLAGS) $(IMPORTS) -i tests/scalar.d -of=$@

bench-certificates: build/scalar-export
	cd lean && $(LAKE) build
	python3 tools/bench_certificates.py --lake $(LAKE)

# Full verification is fail-closed. Fast compilation alone never grants trust.
verify: test build/qsym
	cd lean && $(LAKE) build
	./build/qsym export build/certificates
	python3 tools/verify.py --lake $(LAKE)

clean:
	rm -rf build
