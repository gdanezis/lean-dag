# Development loop for lean-dag.  Timings below are wall clock on a warm
# cache, measured on a 14-core machine; they are why the targets are split
# the way they are.
#
#   make fast     library only, plus the sub-second checks          ~3s warm
#   make check    both libraries, plus the sub-second checks        ~5s warm
#   make deps     regenerate deps.tsv and the support diagrams       ~6s
#   make pdf      the report PDF                                     ~2s
#   make verify   everything, in the order a commit needs it        ~15s
#
# `make fast` skips the witness layer (LeanDagTest) and the dependency
# extraction.  A cold `make fast` is 119s against 325s for a cold `make
# check`, because the witnesses are `decide` over concrete models and cost
# about 11s each.  Run `make check` before committing: the witnesses are a
# default lake target on purpose, so that a definition change which empties
# the concrete structures fails the build instead of silently trivialising
# every theorem above it.
#
# `make deps` is separate because `scripts/DepGraph.lean` walks the whole
# compiled environment.  Nothing it produces changes unless a declaration
# is added, renamed or removed, so it does not belong in the loop.  Run it
# when the set of declarations changes, and before a commit that adds any.

.PHONY: fast check deps pdf verify clean-project help
.DEFAULT_GOAL := help

## fast: library only, plus the checks that cost nothing
fast:
	lake build LeanDag
	python3 scripts/extract-decls.py
	python3 scripts/audit-report.py
	python3 scripts/check-arc-holes.py

## check: both libraries, plus the same checks
check:
	lake build
	python3 scripts/extract-decls.py
	python3 scripts/audit-report.py
	python3 scripts/check-arc-holes.py

## deps: regenerate the dependency graph, after declarations change
deps:
	lake env lean scripts/DepGraph.lean
	python3 scripts/depgraph.py

## pdf: build the report
pdf:
	./scripts/build-pdf.sh docs/report.md docs/pdf/report.pdf

## verify: what a commit needs, in order
verify: check deps pdf

## clean-project: drop this project's build artifacts, keeping Mathlib's
clean-project:
	find .lake/build/lib -path "*LeanDag*" \
	  \( -name "*.olean" -o -name "*.ilean" -o -name "*.trace" -o -name "*.hash" \) -delete

help:
	@grep -E '^## ' $(MAKEFILE_LIST) | sed 's/^## /  make /'
