DC ?= ldc2
LAKE ?= lake
UTIL_PARENT ?= deps
DFLAGS ?= -O -boundscheck=on
VERIFYFLAGS ?=
MODULES := $(wildcard *.d)
GENERATED_D := generated/rules.d
GENERATED_LEAN := lean/QSym/Generated.lean
IMPORTS := -I.. -I$(UTIL_PARENT)

.PHONY: all generate test demo verify bench bench-certificates bench-associative bench-sums bench-counted clean
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
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/predicates.d -of=build/predicate-tests
	./build/predicate-tests --DRT-testmode=run-main build/predicates
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/quadratics.d -of=build/quadratic-tests
	./build/quadratic-tests --DRT-testmode=run-main build/quadratics
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/order.d -of=build/order-tests
	./build/order-tests --DRT-testmode=run-main build/order
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/guards.d -of=build/guard-tests
	./build/guard-tests --DRT-testmode=run-main build/guards
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/folding.d -of=build/folding-tests
	./build/folding-tests --DRT-testmode=run-main build/folding
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/relations.d -of=build/relation-tests
	./build/relation-tests --DRT-testmode=run-main build/relations
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/identities.d -of=build/identity-tests
	./build/identity-tests --DRT-testmode=run-main build/identities
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/compact.d -of=build/compact-tests
	./build/compact-tests --DRT-testmode=run-main build/compact
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/associative.d -of=build/associative-tests
	./build/associative-tests --DRT-testmode=run-main build/associative
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/regions.d -of=build/region-tests
	./build/region-tests --DRT-testmode=run-main build/regions
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/counted.d -of=build/counted-tests
	./build/counted-tests --DRT-testmode=run-main build/counted
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/signs.d -of=build/sign-tests
	./build/sign-tests --DRT-testmode=run-main build/signs
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/sum.d -of=build/sum-tests
	./build/sum-tests --DRT-testmode=run-main build/sum
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/rational.d -of=build/rational-tests
	./build/rational-tests --DRT-testmode=run-main build/rational
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

build/associative-bench: generate tools/bench_associative.d $(MODULES)
	$(DC) $(DFLAGS) $(IMPORTS) -i tools/bench_associative.d -of=$@

bench-associative: build/associative-bench
	./build/associative-bench build/bench-associative
	cd lean && $(LAKE) build
	python3 tools/bench_certificates.py --exporter build/associative-bench --lake $(LAKE)

build/sum-bench: generate tools/bench_sums.d $(MODULES)
	$(DC) $(DFLAGS) $(IMPORTS) -i tools/bench_sums.d -of=$@

bench-sums: build/sum-bench
	cd lean && $(LAKE) build
	python3 tools/profile_certificates.py --lake $(LAKE)

build/counted-bench: generate tools/bench_counted.d $(MODULES)
	$(DC) $(DFLAGS) $(IMPORTS) -i tools/bench_counted.d -of=$@

bench-counted: build/counted-bench
	./build/counted-bench build/bench-counted
	cd lean && $(LAKE) build
	python3 tools/bench_certificates.py --exporter build/counted-bench --lake $(LAKE)

# Full verification is fail-closed. Fast compilation alone never grants trust.
verify: test build/qsym
	cd lean && $(LAKE) build
	./build/qsym export build/certificates
	python3 tools/verify.py --lake $(LAKE) $(VERIFYFLAGS)

clean:
	rm -rf build
