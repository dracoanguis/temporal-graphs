# temporal-graph

This library constructed on top of the mathlib introduces simple temporal graphs and associated structures.
Moreover, it tries to prove the bound on existence of `O(n log n)` size spanner for temporal cliques.

## Blueprint

A [blueprint](blueprint/) documents the mathematical content and its Lean formalization
status (definitions, theorems, dependency graph). Building it requires a TeX distribution
(e.g. `brew install --cask basictex`, then `sudo tlmgr install latexmk collection-latexextra`)
and `graphviz` (`brew install graphviz`) for the dependency graph. Then:

    python3 -m venv blueprint/.venv
    blueprint/.venv/bin/pip install -r blueprint/requirements.txt
    export PATH="$PWD/blueprint/.venv/bin:$PATH"
    leanblueprint web   # or: leanblueprint pdf

then open `blueprint/web/index.html` (or `blueprint/print/print.pdf`).