# temporal-graphs

A Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4) library on **temporal
graphs** — graphs whose edges are labelled by the (natural-number) times at which they are
available. It is developed as part of the master's thesis *Temporal Graphs in Lean: A
beginner's journey to assisted formal proof* (Ethan Bargaud-Arm, Université de Genève,
supervised by Pr. Karine Altisen and Pr. Arnaud Casteigts).

Unlike in static graphs, reachability in a temporal graph is defined by the existence of a
*walk* whose edge times are non-decreasing, which makes classical connectivity results fail to
transfer directly. The library's target result is that every **temporal clique** (a temporal
graph whose footprint is complete) admits a **spanner** — a sparse reachability-preserving
subgraph — of size `O(n log n)`. This was first shown by Casteigts, Peters & Schoeters, combining
*dismountability* with other techniques (*Temporal Cliques Admit Sparse Spanners*, ICALP 2019 /
JCSS 2021). Angrick et al. (ESA 2024) simplified the second half of that proof with a one-sided
variant of dismountability, and Carnevale, Casteigts & Corsini (*Dismountability in Temporal
Cliques Revisited*, SAND 2025) showed that the whole result follows from dismountability alone:
excluding 1- and 2-hop dismountability reduces temporal cliques to bi-cliques, where the
one-sided argument concludes. This library follows the SAND 2025 proof, its main reference; the
clique-side structure (SAND §§2–3) is formalized so far.

Since Mathlib does not (yet) support temporal graphs, this library builds the required theory
from scratch, following Mathlib's `SimpleGraph` conventions so that it can, in principle, later
be upstreamed.

## Design

The central type is `TemporalGraph V`, an *unbundled* structure carrying only the adjacency
relation `Adj : V → V → ℕ → Prop`. Symmetry and irreflexivity ("looplessness") are expressed as
type classes, `IsSymm`/`IsLoopless`, taken as instance arguments (`[G.IsSymm]`, `[G.IsLoopless]`)
and resolved automatically wherever needed, rather than as bundled fields of the structure or
hypotheses threaded by hand. `IsSimple`/`IsClique`/`IsProper`/`IsHappy` stay plain predicates —
they don't need the same cross-cutting instance resolution.

## Library layout

| File | Contents |
|---|---|
| `TemporalGraph/Init.lean` | The `TemporalGraph` aesop rule-set used by the `aesop_temporal_graph` macro |
| `TemporalGraph/Basic.lean` | `TemporalGraph V`; the `IsSymm`/`IsLoopless` classes; `IsSimple`/`IsProper`/`IsHappy`; `IsClique` (takes a vertex set `S : Set V`, Mathlib-style) and its shorthand `IsCliqueGraph` (`IsClique Set.univ`); `footprint` (→ `Digraph`), `simpleFootprint` (→ `SimpleGraph`, given proofs of `IsSymm`/`IsLoopless`); earliest/latest edges and neighbors; `IsSubgraphOf`/`IsSpanningSubgraph`; `neighborSet`; `arcSet`/`arcSize` (oriented world); `edgeSet`/`size` (symmetric world; `mem_edgeSet` needs only `[IsSymm]`) |
| `TemporalGraph/NonemptyTemporalWalk.lean`, `TemporalGraph/TemporalWalk.lean` | Non-strict, time-non-decreasing temporal walks (journeys), split into nonempty/empty variants |
| `TemporalGraph/Subgraph.lean` | The `Subgraph` type, which extends `TemporalGraph V`, adding a field `verts`/proofs `adj_sub`/`edge_vert`/`edge_vert'`; its coercion `coe` to `TemporalGraph H.verts`; inherited predicates `IsSymm`/`IsSimple`/`IsProper`/`IsHappy` and earliest/latest edge/neighbor definitions, and inherited `edgeSet` (not redefined); the subgraph-specific `neighborSet`/`size`/`incidenceSet`, and `IsCliqueSubgraph` (the shorthand for `IsClique H.verts`, i.e., cliqueness via the inherited predicate); and the `induce`/`deleteVerts`/`addVerts`/`addArc`/`addEdge`/`toSubgraph`/`fromEdgeSet` constructions (`addArc` adds a single oriented edge with no hypothesis, `addEdge` adds both orientations and needs `[G.IsSymm]`) |
| `TemporalGraph/Bipartite.lean` | Bipartite temporal graphs: `IsBipartiteWith` and `IsBipartite` (mirroring Mathlib's `SimpleGraph.IsBipartiteWith`), with a bridge `isBipartiteWith_iff_simpleFootprint` to Mathlib's bipartiteness via simple footprint; the `between` construction restricting edges to a cut; temporal bi-cliques `IsBicliqueWith`/`IsBiclique` (SAND 2025 §1.1, taking a vertex set `S : Set V`) and the `completeBipartite` constructor; analogous predicates and operations at the subgraph level (`Subgraph.between`) |
| `TemporalGraph/Connectivity/Basic.lean`, `TemporalGraph/Connectivity/Subgraph.lean` | `Reachable` and temporal connectivity (the top-level `IsSpanner`/`IsTCSpanner` are commented out pending design review); the live spanner notions `Subgraph.IsSpanner`, `Subgraph.IsSpannerOf`, `Subgraph.IsTCSpanner` |
| `TemporalGraph/Dismountability/Basic.lean` | The `Dismountable` property (SAND §2, the hypothesis of Theorem 1) and `TwoHopDismountable` (SAND §2.1, unnumbered) and the vertex sets `vminus`/`vplus`/`vzero` (SAND §3.1, unnumbered), characterized by `partition_of_not_dismountable` (SAND Lemma 2), `vplus_ne_neighbor_of_not_twoHopDismountable`/`vminus_ne_neighbor_of_not_twoHopDismountable` (SAND Lemma 3), the `earliestNeighborFn`/`latestNeighborFn` bijections together with `existsUnique_vplus_earliestEdge`/`existsUnique_vminus_latestEdge`/`vminus_card_eq_vplus_card` (SAND Corollary 4), and `vzero_empty_of_not_twoHopDismountable` (SAND Lemma 5) |
| `TemporalGraph/Dismountability/Operations.lean` | The `dismount`/`mount`/`twoHopMount` operations and their correctness theorems: `dismountability` (SAND Theorem 1, 1-hop dismountability) and `twoHopDismountability` (its 2-hop analogue) |
| `TemporalGraph.lean` (root) | Import aggregator for the whole library — no longer carries demo content |
| `TemporalGraph/Examples.lean` | Worked example: the `square` temporal clique (four vertices, edges at times 1–4) |

## Main formalized result

In a non-2-hop-dismountable (happy) temporal clique, every vertex is either the earliest or the
latest neighbor of some other vertex — i.e. `vzero = ∅` (SAND Lemma 5). Together with the
earliest/latest-neighbor bijections between `vminus` and `vplus` (SAND Corollary 4), this gives
the V⁻/V⁺ perfect-matching structure that is the bridge used by the source papers toward the
`O(n log n)` spanner bound.

## References

1. Daniele Carnevale, Arnaud Casteigts & Timothée Corsini, *Dismountability in Temporal Cliques
   Revisited*, SAND 2025, LIPIcs 330, 6:1–6:18. doi:10.4230/LIPIcs.SAND.2025.6, arXiv:2502.01321.
   Main reference: the proof this library formalizes.
2. Arnaud Casteigts, Joseph G. Peters & Jason Schoeters, *Temporal Cliques Admit Sparse
   Spanners*, ICALP 2019 / JCSS 2021. Original source of the dismountability technique and the
   `O(n log n)` spanner bound.
3. Angrick et al., ESA 2024 — cited above (introduction) for the observation the SAND 2025 proof
   builds on.

## Blueprint

A [blueprint](blueprint/) documents the mathematical content and its Lean formalization
status (definitions, theorems, dependency graph). Its Python environment is a
[uv](https://docs.astral.sh/uv/) project ([`blueprint/pyproject.toml`](blueprint/pyproject.toml),
locked by `blueprint/uv.lock`): `uv run` creates `blueprint/.venv` on first use, so there is no
manual venv step. Nothing TeX-related is installed outside that environment:

- the HTML version is rendered by plasTeX alone. The only TeX program plasTeX needs,
  `kpsewhich` (to resolve `\input{macros/...}`), is a small script of the uv project
  ([`blueprint/blueprint_tools/`](blueprint/blueprint_tools/), installed into `blueprint/.venv/bin`);
- the PDF version uses xelatex from a pinned [TinyTeX](https://yihui.org/tinytex/) that
  `uv run --project blueprint install-tinytex` downloads once into `blueprint/.venv/tinytex`
  (about 250 MB, plus the few LaTeX packages `print.tex` needs). The environment's `latexmk`
  script runs it, so deleting `blueprint/.venv` removes TeX too.

The one system requirement is `graphviz` (`brew install graphviz`), which `pygraphviz` links
against for the dependency graph. From the repository root:

    uv run --project blueprint leanblueprint web          # HTML → blueprint/web/index.html
    uv run --project blueprint install-tinytex            # once, before the first PDF build
    uv run --project blueprint leanblueprint pdf          # PDF  → blueprint/print/print.pdf
    uv run --project blueprint leanblueprint checkdecls   # declarations exist (after `lake build`)
    uv run --project blueprint leanblueprint serve        # preview the HTML version locally

`checkdecls` is a Lake dependency of this package, used only for that check. If a PDF build
fails, delete `blueprint/print/` before retrying: latexmk otherwise refuses to rerun after an
error.

## API documentation

The API documentation is generated by [doc-gen4](https://github.com/leanprover/doc-gen4) from
the separate Lake project [`docbuild/`](docbuild/), so the library itself does not depend on
doc-gen4. The project mirrors the one `docgen-action` generates in CI. It shares this package's
`.lake/packages`, so the Mathlib build fetched by `lake exe cache get` is reused, not rebuilt:

    lake exe cache get                                          # once, at the repository root
    cd docbuild && DOCGEN_SRC=file lake build TemporalGraph:docs  # → docbuild/.lake/build/doc/index.html

`DOCGEN_SRC=file` makes source links point to local files. The default (`github`) derives them
from the `origin` remote and fails, because this repository's remote is on GitLab.

The first run is long, but no Lean code is recompiled. doc-gen4 extracts the documentation data
(`:docInfo`) of every imported module, nearly all of Mathlib, into one SQLite database, and it
has no option to skip dependencies. On the author's machine this took about three hours. Later
runs are incremental: only this library's modules are redone, in a few minutes. Changing
`DOCGEN_SRC` does not invalidate the dependencies' data. When `lean-toolchain` changes, update the doc-gen4 `rev` in
`docbuild/lakefile.toml` to the same tag and run `lake update doc-gen4` in `docbuild/`.

## Building

The toolchain (`lean`, `lake`, `elan`) is pinned by [`lean-toolchain`](lean-toolchain); install
it with [elan](https://github.com/leanprover/elan) if needed.

```sh
lake build                                  # every module of the library
lake build TemporalGraph.Dismountability.Operations   # one module, with its dependencies
lake env lean TemporalGraph/<File>.lean     # typecheck a single file in isolation
```

The library target declares `globs = ["TemporalGraph.*"]`, so `lake build` covers every module,
including the root `TemporalGraph` itself (`.+` would match only its strict submodules and skip the
root, which `checkdecls` imports).
Without it, lake would build only the root module `TemporalGraph.lean` and what it imports, which
stops at `Subgraph` and silently skips `Connectivity/` and `Dismountability/`.

## Status

This library is under active development alongside the thesis. `TemporalGraph` and `Subgraph`
follow an unbundled design: both types carry only data (`Adj`, and `verts` for a subgraph).
Symmetry and irreflexivity are expressed as type classes (`IsSymm`/`IsLoopless`), passed via
instance resolution rather than explicit hypotheses — results that need them take `[G.IsSymm]`
or `[G.IsLoopless]`, and constructions that preserve them declare instances. This departs from
Mathlib's `SimpleGraph`, which bundles `symm` and `loopless` as structure fields; the motivation
is to avoid threading hypotheses through 82 declarations only to use them in 13, and to let a
subgraph be oriented. `Subgraph` now extends `TemporalGraph`, eliminating duplication: `IsSymm`,
`IsSimple`, `IsProper`, `IsHappy`, `EarliestEdge`, `LatestEdge`, `EarliestNeighbor` and
`LatestNeighbor` are now inherited through the parent projection `toTemporalGraph`, not
redefined. The oriented world has its own edge measure: `arcSet` and `arcSize` count ordered
pairs (no hypothesis), while `edgeSet` and `size` count unordered edges (`mem_edgeSet` requires
only `[IsSymm]`).

Every module typechecks and the library contains no `sorry`.

## License

Apache License 2.0 — see [`LICENSE.md`](LICENSE.md).
