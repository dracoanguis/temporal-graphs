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
subgraph — of size `O(n log n)`. This was first shown by Casteigts, Peters & Schoeters via the
technique of *dismountability* (*Temporal Cliques Admit Sparse Spanners*, ICALP 2019 / JCSS
2021), and later reproved more simply with a one-sided variant of the same idea by Carnevale,
Casteigts & Corsini (*Dismountability in Temporal Cliques Revisited*, SAND 2025), building on an
observation of Angrick et al. (ESA 2024). This library formalizes the simplified proof.

Since Mathlib does not (yet) support temporal graphs, this library builds the required theory
from scratch, following Mathlib's `SimpleGraph` conventions so that it can, in principle, later
be upstreamed.

## Library layout

| File | Contents |
|---|---|
| `TemporalGraph/Init.lean` | The `LooplessTemporalGraph` aesop rule-set used by the `aesop_temporal_graph` macro |
| `TemporalGraph/Basic.lean` | The core bundled type `LooplessTemporalGraph V` (`Adj`, `symm`, `loopless`); `IsSimple`/`IsProper`/`IsHappy`/`IsClique`; `Footprint` (→ Mathlib `SimpleGraph`); earliest/latest edges and neighbors; `EdgeSet`/`size` |
| `TemporalGraph/NonemptyTemporalWalk.lean`, `TemporalGraph/TemporalWalk.lean` | Non-strict, time-non-decreasing temporal walks (journeys), split into nonempty/empty variants with coercions between them |
| `TemporalGraph/SubTemporalGraph.lean` | The bundled `SubTemporalGraph` type, its two coercions back to a `LooplessTemporalGraph` (on `Set V` or on `V`), spanning/spanner predicates, and the `addVerts`/`addEdge` operations |
| `TemporalGraph/Connectivity/Basic.lean`, `TemporalGraph/Connectivity/SubTemporalGraph.lean` | `Reachable`, temporal connectivity (`TC`/`TC<`), and temporal spanners |
| `TemporalGraph/Dismountability/Basic.lean` | Earliest/latest-edge extension lemmas; the `Dismountable`/`TwoHopDismountable` properties; the vertex sets `Vplus`/`Vminus`/`Vzero` and their characterization (Lemmas/Theorems 3.1–3.4 of Casteigts–Peters–Schoeters) |
| `TemporalGraph/Dismountability/Operations.lean` | The `dismount`/`mount`/`twoHopMount` operations and their correctness theorems (`dismountability`, `twoHopDismountability`) |
| `TemporalGraph.lean` (root) | Scratch/demo file (currently commented out) |

## Main formalized result

In a non-2-hop-dismountable (happy) temporal clique, every vertex is either the earliest or the
latest neighbor of some other vertex — i.e. `Vzero = ∅` (`vzero_empty_of_not_twoHopDismountable`
in `Dismountability/Basic.lean`). This reduces such cliques to a bipartite structure on
`Vplus`/`Vminus`, which is the bridge used by the source papers to obtain the `O(n log n)`
spanner bound.

## Building

The toolchain (`lean`, `lake`, `elan`) is pinned by [`lean-toolchain`](lean-toolchain)
(currently `leanprover/lean4:v4.29.0-rc6`); install it with [elan](https://github.com/leanprover/elan)
if needed.

```sh
lake build                                  # full build
lake env lean TemporalGraph/<File>.lean     # typecheck a single file in isolation
```

## Status / further work

- The `O(n log n)` size bound for fully (two-hop-)dismountable cliques is not yet formalized in
  general; only the one-hop case's per-step size bound is proved.
- A `k`-hop generalization of dismountability is a natural, if tedious, extension not yet
  explored.
- A more recent result (Baligacs, *Temporal Cliques Admit Linear Spanners*, arXiv:2606.05156)
  gives a linear `7n`-size spanner via a related biclique reduction; formalizing it is a natural
  continuation but is not part of this library yet.
- Long-term goal: upstream this library into Mathlib, starting with `LooplessTemporalGraph` and
  `SubTemporalGraph`.

## License

Apache License 2.0 — see [`LICENSE.md`](LICENSE.md).
