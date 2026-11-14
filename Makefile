# Requires GNU Make 4.3 or newer (grouped generator outputs).
DC ?= ldc2
LAKE ?= lake
UTIL_PARENT ?= deps
DFLAGS ?= -O -boundscheck=on
VERIFYFLAGS ?=
MODULES := $(wildcard *.d)
UTIL_MODULES := $(wildcard $(UTIL_PARENT)/util/*.d)
GENERATED_D := generated/rules.d
GENERATED_LEAN := lean/QSym/Generated.lean
IMPORTS := -I.. -I$(UTIL_PARENT)

.PHONY: all generate build-tests test test-edit-motion test-progress demo verify verify-full bench bench-certificates bench-associative bench-sums bench-counted bench-joins clean
.DELETE_ON_ERROR:
all: build/qsym

build generated:
	mkdir -p $@

build/rulec: tools/rulec.d $(MODULES) $(UTIL_MODULES) Makefile | build
	$(DC) $(DFLAGS) $(IMPORTS) -i tools/rulec.d -of=$@

generate: $(GENERATED_D) $(GENERATED_LEAN)

# Grouped targets ensure only one generator runs, including under make -j.
$(GENERATED_D) $(GENERATED_LEAN) &: rules/core.qs build/rulec | generated
	./build/rulec rules/core.qs $(GENERATED_D) $(GENERATED_LEAN)

build/qsym: $(GENERATED_D) $(GENERATED_LEAN) Makefile $(UTIL_MODULES) tools/main.d tools/repl.d tools/lineedit.d tools/edit.d tools/unicode.d $(MODULES)
	$(DC) $(DFLAGS) $(IMPORTS) -i tools/main.d -of=$@

build/edit-motion-tests: tests/edit_motion.d tools/edit.d tools/unicode.d Makefile | build
	$(DC) -boundscheck=on $(IMPORTS) -i tests/edit_motion.d -of=$@

test-edit-motion: build/edit-motion-tests
	./build/edit-motion-tests

# Compile the shared engine once per test mode; each executable keeps its own
# main, unittest set, and certificate output directory. For example:
#   make -j4 build-tests    # compile only
#   make -j4 test          # compile in parallel, then run every suite
#   make -j4 verify        # same builds, followed by the existing Lean checks
TEST_DFLAGS ?= -boundscheck=on

build/libqsym-test.a: $(MODULES) $(GENERATED_D) $(UTIL_MODULES) Makefile | build
	rm -f $@
	$(DC) $(TEST_DFLAGS) $(IMPORTS) -lib -i $(MODULES) -od=build/test-core -of=$@

build/libqsym-test-unit.a: $(MODULES) $(GENERATED_D) $(UTIL_MODULES) Makefile | build
	rm -f $@
	$(DC) $(TEST_DFLAGS) -unittest $(IMPORTS) -lib -i $(MODULES) -od=build/test-core-unit -of=$@

# Syntax tests supply a different qsym.generated.rules, so they must not link
# against the shared engine archive containing the production rules.
build/syntax.d build/Syntax.lean &: tests/syntax.qs build/rulec | build
	./build/rulec tests/syntax.qs build/syntax.d build/Syntax.lean

build/syntax-tests: tests/generated.d build/syntax.d build/Syntax.lean $(MODULES) $(UTIL_MODULES) Makefile
	$(DC) $(TEST_DFLAGS) -unittest $(IMPORTS) -i tests/generated.d build/syntax.d -of=$@

build/tests: tests/all.d tests/rules.d tools/edit.d tools/unicode.d build/libqsym-test-unit.a Makefile
	$(DC) $(TEST_DFLAGS) -unittest $(IMPORTS) tests/all.d tests/rules.d tools/edit.d tools/unicode.d build/libqsym-test-unit.a -of=$@

TEST_BINARIES := build/tests build/syntax-tests build/edit-motion-tests

# $(1): executable name; $(2): source; $(3): optional unittest flag.
define test_binary
TEST_BINARIES += build/$(1)
build/$(1): tests/$(2).d build/libqsym-test$(if $(3),-unit).a Makefile
	$$(DC) $$(TEST_DFLAGS) $(3) $$(IMPORTS) $$< build/libqsym-test$(if $(3),-unit).a -of=$$@
endef

$(eval $(call test_binary,summation-tests,summation,))
$(eval $(call test_binary,summation-tail-tests,summation_tails,))
$(eval $(call test_binary,scalar-tests,scalar,-unittest))
$(eval $(call test_binary,language-tests,language,-unittest))
$(eval $(call test_binary,elementary-tests,elementary,-unittest))
$(eval $(call test_binary,transcendental-tests,transcendental,-unittest))
$(eval $(call test_binary,trig-magnitude-tests,trig_magnitudes,))
$(eval $(call test_binary,indexed-norm-tests,indexed_norms,))
$(eval $(call test_binary,sqrt-product-tests,sqrt_products,))
$(eval $(call test_binary,zero-power-tests,zero_powers,))
$(eval $(call test_binary,argument-composition-tests,argument_compositions,))
$(eval $(call test_binary,atanh-composition-tests,atanh_compositions,))
$(eval $(call test_binary,inverse-symmetry-tests,inverse_symmetry,))
$(eval $(call test_binary,sqrt-branch-tests,sqrt_branches,))
$(eval $(call test_binary,power-tests,powers,-unittest))
$(eval $(call test_binary,function-tests,functions,-unittest))
$(eval $(call test_binary,exponential-tests,exponentials,-unittest))
$(eval $(call test_binary,trigonometry-tests,trigonometry,-unittest))
$(eval $(call test_binary,radical-tests,radicals,-unittest))
$(eval $(call test_binary,inverse-tests,inverses,-unittest))
$(eval $(call test_binary,domain-tests,domains,-unittest))
$(eval $(call test_binary,predicate-tests,predicates,-unittest))
$(eval $(call test_binary,quadratic-tests,quadratics,-unittest))
$(eval $(call test_binary,order-tests,order,-unittest))
$(eval $(call test_binary,guard-tests,guards,-unittest))
$(eval $(call test_binary,guard-budget-tests,guard_budget,))
$(eval $(call test_binary,folding-tests,folding,-unittest))
$(eval $(call test_binary,relation-tests,relations,-unittest))
$(eval $(call test_binary,identity-tests,identities,-unittest))
$(eval $(call test_binary,compact-tests,compact,-unittest))
$(eval $(call test_binary,associative-tests,associative,-unittest))
$(eval $(call test_binary,region-tests,regions,-unittest))
$(eval $(call test_binary,counted-tests,counted,-unittest))
$(eval $(call test_binary,join-tests,joins,-unittest))
$(eval $(call test_binary,lookup-tests,lookup,-unittest))
$(eval $(call test_binary,sign-tests,signs,-unittest))
$(eval $(call test_binary,sum-tests,sum,-unittest))
$(eval $(call test_binary,rational-tests,rational,-unittest))
$(eval $(call test_binary,discrete-tests,discrete,-unittest))
$(eval $(call test_binary,trig-algebra-tests,trig_algebra,-unittest))
$(eval $(call test_binary,assumption-tests,assumptions,-unittest))
$(eval $(call test_binary,numeral-tests,numerals,-unittest))
$(eval $(call test_binary,bounds-tests,bounds,-unittest))
$(eval $(call test_binary,subtype-tests,subtypes,-unittest))
$(eval $(call test_binary,convergence-tests,convergence,-unittest))
$(eval $(call test_binary,control-tests,control,-unittest))
$(eval $(call test_binary,partition-tests,partitions,-unittest))
$(eval $(call test_binary,binding-tests,binding,-unittest))
$(eval $(call test_binary,functional-tests,functional,-unittest))
$(eval $(call test_binary,subset-tests,subsets,-unittest))
$(eval $(call test_binary,refinement-tests,refinements,-unittest))
$(eval $(call test_binary,type-value-tests,type_values,-unittest))
$(eval $(call test_binary,recursion-tests,recursion,-unittest))
$(eval $(call test_binary,higher-equality-tests,higher_equality,-unittest))
$(eval $(call test_binary,binder-name-tests,binder_names,-unittest))
$(eval $(call test_binary,recurrence-solver-tests,recurrences,-unittest))
$(eval $(call test_binary,affine-recurrence-tests,affine_recurrences,-unittest))
$(eval $(call test_binary,linear-recurrence-tests,linear_recurrences,-unittest))
$(eval $(call test_binary,spectral-tests,spectral,))
$(eval $(call test_binary,integer-spectra-tests,integer_spectra,))
$(eval $(call test_binary,tensor-domain-tests,tensor_domains,))
$(eval $(call test_binary,matrix-block-tests,matrix_blocks,))
$(eval $(call test_binary,discrete-interval-tests,discrete_intervals,))
$(eval $(call test_binary,repeated-spectra-tests,repeated_spectra,))
$(eval $(call test_binary,nilpotent-spectra-tests,nilpotent_spectra,))
$(eval $(call test_binary,cube-zero-spectra-tests,cube_zero_spectra,))
$(eval $(call test_binary,zero-root-spectra-tests,zero_root_spectra,))
$(eval $(call test_binary,cutoff-tests,cutoff,-unittest))
$(eval $(call test_binary,tensor-tests,tensors,-unittest))
$(eval $(call test_binary,dependent-tests,dependent,-unittest))
$(eval $(call test_binary,interval-tests,intervals,-unittest))
$(eval $(call test_binary,fixed-domain-tests,fixed_domains,-unittest))
$(eval $(call test_binary,partial-domain-tests,partial_domains,-unittest))
$(eval $(call test_binary,ranked-domain-tests,ranked_domains,))
$(eval $(call test_binary,real-countdown-tests,real_countdown,-unittest))
$(eval $(call test_binary,argument-branch-tests,argument_branches,))
$(eval $(call test_binary,argument-rotation-tests,argument_rotation,))
$(eval $(call test_binary,recovered-algebra-tests,recovered_algebra,))

build-tests: $(TEST_BINARIES)

test: build-tests build/qsym
	./build/summation-tests build/summation
	./build/summation-tail-tests build/summation-tails
	./build/edit-motion-tests
	./build/tests
	./build/syntax-tests
	./build/scalar-tests --DRT-testmode=run-main build/scalar
	./build/language-tests --DRT-testmode=run-main build/language
	./build/elementary-tests --DRT-testmode=run-main build/elementary
	./build/transcendental-tests --DRT-testmode=run-main build/transcendental
	./build/trig-magnitude-tests build/trig-magnitudes
	./build/indexed-norm-tests build/indexed-norms
	./build/sqrt-product-tests build/sqrt-products
	./build/zero-power-tests build/zero-powers
	./build/argument-composition-tests build/argument-compositions
	./build/atanh-composition-tests build/atanh-compositions
	./build/inverse-symmetry-tests build/inverse-symmetry
	./build/sqrt-branch-tests build/sqrt-branches
	./build/power-tests --DRT-testmode=run-main build/powers
	./build/function-tests --DRT-testmode=run-main build/functions
	./build/exponential-tests --DRT-testmode=run-main build/exponentials
	./build/trigonometry-tests --DRT-testmode=run-main build/trigonometry
	./build/radical-tests --DRT-testmode=run-main build/radicals
	./build/inverse-tests --DRT-testmode=run-main build/inverses
	./build/domain-tests --DRT-testmode=run-main build/domains
	./build/predicate-tests --DRT-testmode=run-main build/predicates
	./build/quadratic-tests --DRT-testmode=run-main build/quadratics
	./build/order-tests --DRT-testmode=run-main build/order
	./build/guard-tests --DRT-testmode=run-main build/guards
	./build/guard-budget-tests build/guard-budget
	./build/folding-tests --DRT-testmode=run-main build/folding
	./build/relation-tests --DRT-testmode=run-main build/relations
	./build/identity-tests --DRT-testmode=run-main build/identities
	./build/compact-tests --DRT-testmode=run-main build/compact
	./build/associative-tests --DRT-testmode=run-main build/associative
	./build/region-tests --DRT-testmode=run-main build/regions
	./build/counted-tests --DRT-testmode=run-main build/counted
	./build/join-tests --DRT-testmode=run-main build/joins
	./build/lookup-tests --DRT-testmode=run-main build/lookup
	./build/sign-tests --DRT-testmode=run-main build/signs
	./build/sum-tests --DRT-testmode=run-main build/sum
	./build/rational-tests --DRT-testmode=run-main build/rational
	./build/discrete-tests --DRT-testmode=run-main build/discrete
	./build/trig-algebra-tests --DRT-testmode=run-main build/trig-algebra
	./build/assumption-tests --DRT-testmode=run-main build/assumptions
	./build/numeral-tests --DRT-testmode=run-main build/numerals
	./build/bounds-tests --DRT-testmode=run-main build/bounds
	./build/subtype-tests --DRT-testmode=run-main build/subtypes
	./build/convergence-tests --DRT-testmode=run-main build/convergence
	./build/control-tests --DRT-testmode=run-main build/control
	./build/partition-tests --DRT-testmode=run-main build/partitions
	./build/binding-tests --DRT-testmode=run-main build/binding
	./build/functional-tests --DRT-testmode=run-main build/functional
	./build/subset-tests --DRT-testmode=run-main build/subsets
	./build/refinement-tests --DRT-testmode=run-main build/refinements
	./build/type-value-tests --DRT-testmode=run-main build/type-values
	./build/recursion-tests --DRT-testmode=run-main build/recursion
	./build/higher-equality-tests --DRT-testmode=run-main build/higher-equality
	./build/binder-name-tests --DRT-testmode=run-main build/binder-names
	./build/recurrence-solver-tests --DRT-testmode=run-main build/recurrences
	./build/affine-recurrence-tests --DRT-testmode=run-main build/affine-recurrences
	./build/linear-recurrence-tests --DRT-testmode=run-main build/linear-recurrences
	./build/spectral-tests build/spectral
	./build/integer-spectra-tests build/integer-spectra
	./build/tensor-domain-tests build/tensor-domains
	./build/matrix-block-tests build/matrix-blocks
	./build/discrete-interval-tests build/discrete-intervals
	./build/repeated-spectra-tests build/repeated-spectra
	./build/nilpotent-spectra-tests build/nilpotent-spectra
	./build/cube-zero-spectra-tests build/cube-zero-spectra
	./build/zero-root-spectra-tests build/zero-root-spectra
	./build/cutoff-tests --DRT-testmode=run-main build/cutoff
	./build/tensor-tests --DRT-testmode=run-main build/tensors
	./build/dependent-tests --DRT-testmode=run-main build/dependent
	./build/interval-tests --DRT-testmode=run-main build/intervals
	./build/fixed-domain-tests --DRT-testmode=run-main build/fixed-domains
	./build/partial-domain-tests --DRT-testmode=run-main build/partial-domains
	./build/ranked-domain-tests build/ranked-domains
	./build/real-countdown-tests --DRT-testmode=run-main build/real-countdown
	./build/argument-branch-tests build/argument-branches
	./build/argument-rotation-tests build/argument-rotation
	./build/recovered-algebra-tests build/recovered-algebra
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
