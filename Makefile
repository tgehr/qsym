DC ?= ldc2
LAKE ?= lake
UTIL_PARENT ?= deps
DFLAGS ?= -O -boundscheck=on
VERIFYFLAGS ?=
MODULES := $(wildcard *.d)
GENERATED_D := generated/rules.d
GENERATED_LEAN := lean/QSym/Generated.lean
IMPORTS := -I.. -I$(UTIL_PARENT)

.PHONY: all generate test test-progress demo verify verify-full bench bench-certificates bench-associative bench-sums bench-counted bench-joins clean
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
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/transcendental.d -of=build/transcendental-tests
	./build/transcendental-tests --DRT-testmode=run-main build/transcendental
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/powers.d -of=build/power-tests
	./build/power-tests --DRT-testmode=run-main build/powers
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/functions.d -of=build/function-tests
	./build/function-tests --DRT-testmode=run-main build/functions
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/exponentials.d -of=build/exponential-tests
	./build/exponential-tests --DRT-testmode=run-main build/exponentials
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/trigonometry.d -of=build/trigonometry-tests
	./build/trigonometry-tests --DRT-testmode=run-main build/trigonometry
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/radicals.d -of=build/radical-tests
	./build/radical-tests --DRT-testmode=run-main build/radicals
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/inverses.d -of=build/inverse-tests
	./build/inverse-tests --DRT-testmode=run-main build/inverses
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/domains.d -of=build/domain-tests
	./build/domain-tests --DRT-testmode=run-main build/domains
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
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/joins.d -of=build/join-tests
	./build/join-tests --DRT-testmode=run-main build/joins
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/lookup.d -of=build/lookup-tests
	./build/lookup-tests --DRT-testmode=run-main build/lookup
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/signs.d -of=build/sign-tests
	./build/sign-tests --DRT-testmode=run-main build/signs
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/sum.d -of=build/sum-tests
	./build/sum-tests --DRT-testmode=run-main build/sum
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/rational.d -of=build/rational-tests
	./build/rational-tests --DRT-testmode=run-main build/rational
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/discrete.d -of=build/discrete-tests
	./build/discrete-tests --DRT-testmode=run-main build/discrete
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/trig_algebra.d -of=build/trig-algebra-tests
	./build/trig-algebra-tests --DRT-testmode=run-main build/trig-algebra
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/assumptions.d -of=build/assumption-tests
	./build/assumption-tests --DRT-testmode=run-main build/assumptions
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/numerals.d -of=build/numeral-tests
	./build/numeral-tests --DRT-testmode=run-main build/numerals
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/bounds.d -of=build/bounds-tests
	./build/bounds-tests --DRT-testmode=run-main build/bounds
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/subtypes.d -of=build/subtype-tests
	./build/subtype-tests --DRT-testmode=run-main build/subtypes
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/convergence.d -of=build/convergence-tests
	./build/convergence-tests --DRT-testmode=run-main build/convergence
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/control.d -of=build/control-tests
	./build/control-tests --DRT-testmode=run-main build/control
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/partitions.d -of=build/partition-tests
	./build/partition-tests --DRT-testmode=run-main build/partitions
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/binding.d -of=build/binding-tests
	./build/binding-tests --DRT-testmode=run-main build/binding
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/functional.d -of=build/functional-tests
	./build/functional-tests --DRT-testmode=run-main build/functional
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/subsets.d -of=build/subset-tests
	./build/subset-tests --DRT-testmode=run-main build/subsets
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/refinements.d -of=build/refinement-tests
	./build/refinement-tests --DRT-testmode=run-main build/refinements
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/type_values.d -of=build/type-value-tests
	./build/type-value-tests --DRT-testmode=run-main build/type-values
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/recursion.d -of=build/recursion-tests
	./build/recursion-tests --DRT-testmode=run-main build/recursion
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/higher_equality.d -of=build/higher-equality-tests
	./build/higher-equality-tests --DRT-testmode=run-main build/higher-equality
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/binder_names.d -of=build/binder-name-tests
	./build/binder-name-tests --DRT-testmode=run-main build/binder-names
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/recurrences.d -of=build/recurrence-solver-tests
	./build/recurrence-solver-tests --DRT-testmode=run-main build/recurrences
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/cutoff.d -of=build/cutoff-tests
	./build/cutoff-tests --DRT-testmode=run-main build/cutoff
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/tensors.d -of=build/tensor-tests
	./build/tensor-tests --DRT-testmode=run-main build/tensors
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/dependent.d -of=build/dependent-tests
	./build/dependent-tests --DRT-testmode=run-main build/dependent
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/intervals.d -of=build/interval-tests
	./build/interval-tests --DRT-testmode=run-main build/intervals
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/fixed_domains.d -of=build/fixed-domain-tests
	./build/fixed-domain-tests --DRT-testmode=run-main build/fixed-domains
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/partial_domains.d -of=build/partial-domain-tests
	./build/partial-domain-tests --DRT-testmode=run-main build/partial-domains
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/real_countdown.d -of=build/real-countdown-tests
	./build/real-countdown-tests --DRT-testmode=run-main build/real-countdown
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

build/join-bench: generate tools/bench_joins.d $(MODULES)
	$(DC) $(DFLAGS) $(IMPORTS) -i tools/bench_joins.d -of=$@

bench-joins: build/join-bench
	./build/join-bench build/bench-joins
	cd lean && $(LAKE) build
	python3 tools/bench_certificates.py --exporter build/join-bench --lake $(LAKE)

# Full verification is fail-closed. Fast compilation alone never grants trust.
verify-full: test build/qsym
	python3 tools/build_lean.py --lake $(LAKE)
	python3 tests/verification.py --lake $(LAKE)
	./build/qsym export build/certificates
	python3 tools/verify.py --lake $(LAKE) $(VERIFYFLAGS)

test-progress:
	python3 tests/progress.py --lake $(LAKE)

verify: test build/qsym
	python3 tools/build_lean.py --lake $(LAKE) --reuse-proofs
	python3 tests/progress.py --lake $(LAKE)
	python3 tests/verification.py --lake $(LAKE)
	./build/qsym export build/certificates
	python3 tools/verify.py --lake $(LAKE) --fast --jobs 2 --batch-size 16 $(VERIFYFLAGS)

clean:
	rm -rf build
