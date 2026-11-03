DC ?= ldc2
LAKE ?= lake
UTIL_PARENT ?= deps
DFLAGS ?= -O -boundscheck=on
MODULES := $(wildcard *.d)
GENERATED_D := generated/rules.d
GENERATED_LEAN := lean/QSym/Generated.lean
IMPORTS := -I.. -I$(UTIL_PARENT)

.PHONY: all generate test demo verify bench clean
all: build/qsym

build generated:
	mkdir -p $@

build/rulec: tools/rulec.d $(MODULES) | build
	$(DC) $(DFLAGS) $(IMPORTS) -i tools/rulec.d -of=$@

generate: build/rulec | generated
	./build/rulec rules/core.qs $(GENERATED_D) $(GENERATED_LEAN)

build/qsym: generate tools/main.d $(MODULES)
	$(DC) $(DFLAGS) $(IMPORTS) -i tools/main.d -of=$@

test: generate
	$(DC) -boundscheck=on -unittest $(IMPORTS) -i tests/all.d -of=build/tests
	./build/tests

demo: build/qsym
	./build/qsym demo

bench: build/qsym
	./build/qsym bench 50000

# Full verification is fail-closed. Fast compilation alone never grants trust.
verify: test build/qsym
	cd lean && $(LAKE) build
	./build/qsym export build/certificates
	python3 tools/verify.py --lake $(LAKE)

clean:
	rm -rf build
