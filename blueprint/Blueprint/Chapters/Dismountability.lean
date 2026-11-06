import Verso
import VersoManual
import VersoBlueprint
import Blueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Dismountability" =>

%%%
tag := "chap:dismountability"
%%%

Formalized in the directory `TemporalGraph/Dismountability/`:

* `Basic.lean`: the partition $`V^-`, $`V^+`, $`V^0`, the bijections, reciprocity, the bi-clique;
* `Operations.lean`: dismount and mount, and the generic clique induction
  ({bpref "thm:clique-induction"}[]), the proof engine shared by both spanner bounds of this
  blueprint;
* `OneSided.lean`: one-sided dismountability;
* `OneSidedBound.lean`: the size of one-sided spanners and the $`O(n \log n)` bound for cliques.

The dismountability technique originates with Casteigts, Peters and Schoeters,
_Temporal Cliques Admit Sparse Spanners_, ICALP 2019 / JCSS. The numbering of the definitions,
lemmas, and theorems below instead follows the more recent treatment by Daniele Carnevale, Arnaud
Casteigts and Timothée Corsini, _Dismountability in Temporal Cliques Revisited_, SAND 2025 (LIPIcs
330, 6:1–6:18, doi:10.4230/LIPIcs.SAND.2025.6, arXiv:2502.01321) — abbreviated SAND below — do
not introduce a different numbering here.

:::definition "def:dismountable" (uses := "def:sub-spanning-clique, def:earliest-latest-neighbor") (lean := "TemporalGraph.Subgraph.Dismountable")
*Dismountable clique — SAND §2, hypothesis of Theorem 2.1.* A clique sub-temporal-graph $`H` of
$`G` _is dismountable_ if it has a vertex that is simultaneously an earliest neighbor of some
vertex and a latest neighbor of some (possibly different) vertex of $`H`.
:::

:::definition "def:vminus-vplus-vzero" (uses := "def:dismountable") (lean := "TemporalGraph.Subgraph.vminus, TemporalGraph.Subgraph.vplus, TemporalGraph.Subgraph.vzero")
*$`V^-`, $`V^+`, $`V^0` — SAND §3.1.* For $`H` a sub-temporal-graph of $`G`: $`V^-(H)` is the
set of vertices that are an earliest neighbor of some vertex of $`H`; $`V^+(H)` is the set of
vertices that are a latest neighbor of some vertex of $`H`; and
$`V^0(H) = \mathrm{Verts}(H) \setminus (V^-(H) \cup V^+(H))`.
:::

:::lemma_ "lem:partition-not-dismountable" (uses := "def:dismountable, def:vminus-vplus-vzero") (lean := "TemporalGraph.Subgraph.partition_of_not_dismountable")
*Partition of non-dismountable cliques — SAND Lemma 3.1.* If $`H` is a clique that is not
dismountable, then $`V^-(H)`, $`V^+(H)`, $`V^0(H)` partition $`\mathrm{Verts}(H)`.
:::

:::proof "lem:partition-not-dismountable" (uses := "lem:dismountable-iff-intersection")
A vertex lying in both $`V^-` and $`V^+` would make $`H` dismountable
({bpref "lem:dismountable-iff-intersection"}[]), so $`V^-` and $`V^+` are disjoint; $`V^0` is by
definition disjoint from both. A case split on $`x \in V^-`, $`x \in V^+` shows that each vertex
of $`H` lies in exactly one of the three sets.
:::

:::lemma_ "lem:vminus-vplus-vzero-decomp" (uses := "def:vminus-vplus-vzero, lem:partition-finite") (lean := "TemporalGraph.Subgraph.vminus_union_vplus_union_vzero")
*Vertex set decomposition.* All three sets $`V^-(H)`, $`V^+(H)`, $`V^0(H)` are subsets of
$`\mathrm{Verts}(H)`, and their union is all of $`\mathrm{Verts}(H)`.
:::

:::proof "lem:vminus-vplus-vzero-decomp"
The inclusions are {bpref "lem:partition-finite"}[]. The union is then $`\mathrm{Verts}(H)` by
set algebra, since $`V^0 = \mathrm{Verts}(H) \setminus (V^- \cup V^+)`.
:::

:::lemma_ "lem:dismountable-iff-intersection" (uses := "def:dismountable, def:vminus-vplus-vzero") (lean := "TemporalGraph.Subgraph.nonempty_vplus_inter_vminus_iff_dismountable")
*Dismountability via intersection.* A clique $`H` is dismountable exactly when
$`V^+(H) \cap V^-(H) \neq \emptyset` — there exists a vertex that is both a latest and an earliest
neighbor.
:::

:::proof "lem:dismountable-iff-intersection"
Unfold the definitions: a vertex that is a latest neighbor of someone and an earliest neighbor of
someone is exactly an element of $`V^+(H) \cap V^-(H)`.
:::

:::definition "def:two-hop-dismountable" (uses := "def:dismountable") (lean := "TemporalGraph.Subgraph.TwoHopDismountable")
*Two-hop dismountable — SAND §2.1.* A clique $`H` is _$`\{1,2\}`-hop dismountable_ if there is a
vertex $`x` such that (earliest side) either $`x` is an earliest neighbor of some vertex, or there
are $`y \neq x` and $`z` such that $`(y,z,n)` is the earliest edge of $`y` and $`z` is joined to
$`x` at a time $`m \le n`; and (latest side) either $`x` is a latest neighbor of some vertex, or
there are $`y \neq x` and $`z` such that $`(y,z,n)` is the latest edge of $`y` and $`z` is joined
to $`x` at a time $`m \ge n`. Every dismountable clique is two-hop dismountable.
:::

:::lemma_ "lem:twoHop-of-dismountable" (uses := "def:dismountable, def:two-hop-dismountable") (lean := "TemporalGraph.Subgraph.twoHopDismountable_of_dismountable")
*Dismountable implies two-hop dismountable.* Every dismountable clique is two-hop dismountable.
:::

:::proof "lem:twoHop-of-dismountable"
Take the same vertex $`x`; the two one-hop alternatives of the definition hold.
:::

:::lemma_ "lem:vplus-vminus-not-neighbors" (uses := "def:two-hop-dismountable, def:vminus-vplus-vzero, def:is-symm-loopless") (lean := "TemporalGraph.Subgraph.vplus_ne_neighbor_of_not_twoHopDismountable, TemporalGraph.Subgraph.vminus_ne_neighbor_of_not_twoHopDismountable")
*Distinct earliest / latest neighbors — SAND Lemma 3.2.* If $`H` is a symmetric clique that is
not two-hop dismountable, then distinct vertices of $`V^+(H)` have distinct earliest neighbors,
and distinct vertices of $`V^-(H)` have distinct latest neighbors.
:::

:::proof "lem:vplus-vminus-not-neighbors" (uses := "def:two-hop-dismountable")
Let $`x \neq y` in $`V^+` with a common earliest neighbor $`z`, at times $`n` (for $`x`) and
$`m` (for $`y`). If $`m \le n`, the vertex $`y` is reached in two hops from the earliest edge
$`(x,z,n)` and the edge $`zy` at $`m \le n` (symmetry), and it is a latest neighbor since
$`y \in V^+`: $`H` is two-hop dismountable at $`y`. If $`m > n`, exchange the roles of $`x` and
$`y`. Both contradict the hypothesis. The statement for $`V^-` and latest neighbors is dual.
:::

:::lemma_ "lem:partition-finite" (uses := "def:vminus-vplus-vzero") (lean := "TemporalGraph.Subgraph.vminus_subset_verts, TemporalGraph.Subgraph.vplus_subset_verts, TemporalGraph.Subgraph.vzero_subset_verts")
*$`V^-`, $`V^+`, $`V^0` are subsets of $`V(H)`.* $`V^-(H)`, $`V^+(H)` and $`V^0(H)` are subsets
of $`\mathrm{Verts}(H)`; in particular they are finite when $`H` has finitely many vertices.
:::

:::proof "lem:partition-finite"
An endpoint of an earliest or latest edge of $`H` is a vertex of $`H`, and $`V^0` is a subset of
$`\mathrm{Verts}(H)` by definition. A subset of a finite set is finite.
:::

:::lemma_ "lem:vzero-empty" (uses := "lem:vplus-vminus-not-neighbors, lem:vminus-vplus-matchings, def:vminus-vplus-vzero, def:is-simple-clique, def:is-proper-happy, def:is-symm-loopless") (lean := "TemporalGraph.Subgraph.vzero_empty_of_not_twoHopDismountable")
*$`V^0` is empty — SAND Lemma 3.4.* If $`H` is a finite, nontrivial, simple, proper, symmetric
clique that is not two-hop dismountable, then $`V^0(H) = \emptyset`: every vertex is an earliest
or a latest neighbor of some vertex.
:::

:::proof "lem:vzero-empty" (uses := "lem:earliestEdge-exists-finite-clique")
Suppose $`x \in V^0`. It has an earliest edge to some $`y \in V^-` at time $`n` and a latest edge
to some $`z \in V^+` at time $`m` ({bpref "lem:earliestEdge-exists-finite-clique"}[]). By the
matchings ({bpref "lem:vminus-vplus-matchings"}[]), $`y` is the endpoint of the earliest edge of
some $`y' \in V^+` at time $`n'`, and $`z` of the latest edge of some $`z' \in V^-` at time
$`m'`. If $`n' \le n`, the vertex $`y'` is reached in two hops from $`x` and is a latest
neighbor, so $`H` is two-hop dismountable at $`y'`; if $`m \le m'`, likewise at $`z'`. Otherwise
$`n < n'` and $`m' < m`, and $`H` is two-hop dismountable at $`x` itself, through $`y'` on the
earliest side and $`z'` on the latest side. Each case contradicts the hypothesis.
:::

# Bijections and cardinality (SAND Corollary 3.3)

:::lemma_ "lem:earliestEdge-exists-finite-clique" (uses := "def:is-simple-clique, def:incidence-set") (lean := "TemporalGraph.Subgraph.exists_earliestEdge_of_isCliqueSubgraph, TemporalGraph.Subgraph.exists_latestEdge_of_isCliqueSubgraph")
*Earliest edges are finitely witnessed.* If $`H` is finite, nontrivial, and a simple clique, then
every vertex has an earliest and a latest edge.
:::

:::proof "lem:earliestEdge-exists-finite-clique" (uses := "lem:earliest-latest-edge-exists")
A nontrivial clique gives every vertex a nonempty incidence set, which is finite since $`H` is
finite and simple; apply {bpref "lem:earliest-latest-edge-exists"}[].
:::

:::lemma_ "lem:earliestEdge-unique-proper-clique" (uses := "def:is-proper-happy, def:is-simple-clique") (lean := "TemporalGraph.Subgraph.existsUnique_earliestEdge_of_isCliqueSubgraph, TemporalGraph.Subgraph.existsUnique_latestEdge_of_isCliqueSubgraph")
*Earliest edges are uniquely witnessed in proper cliques.* If $`H` is finite, nontrivial, and a
simple, proper clique, then each vertex has a unique earliest (resp. latest) edge.
:::

:::proof "lem:earliestEdge-unique-proper-clique" (uses := "lem:earliestEdge-exists-finite-clique")
Existence is the previous lemma. Two earliest edges of $`x` have the same time, both being
minimal; properness then forces the same neighbor.
:::

:::definition "def:neighbor-functions" (uses := "lem:earliestEdge-unique-proper-clique") (lean := "TemporalGraph.earliestNeighborFn, TemporalGraph.latestNeighborFn")
*Earliest/latest neighbor functions.* For any temporal graph $`G`, define
$`\mathrm{f_{ee}}, \mathrm{f_{le}} : V \to V \cup \{\bot\}` (Lean's `Option V`):
$`\mathrm{f_{ee}}(x)` is one of the earliest (resp. latest) neighbors of $`x`, and $`\bot`
(`none`) when $`x` has none. On a finite, nontrivial, simple clique $`H`, they map $`V^+(H)` into
$`V^-(H)`, resp. $`V^-(H)` into $`V^+(H)`.
:::

:::lemma_ "lem:neighbor-fn-eq" (uses := "def:neighbor-functions, def:earliest-latest-neighbor") (lean := "TemporalGraph.earliestNeighborFn_eq_some_iff, TemporalGraph.latestNeighborFn_eq_some_iff")
*Neighbor functions characterize membership.* Let $`G` be a proper temporal graph and
$`x, y \in V` (so $`y \ne \bot`). Then $`\mathrm{f_{ee}}(x) = y` if and only if $`y` is an
earliest neighbor of $`x` (`EarliestNeighbor`), and $`\mathrm{f_{le}}(x) = y` if and only if
$`y` is a latest neighbor of $`x` (`LatestNeighbor`).
:::

:::proof "lem:neighbor-fn-eq" (uses := "lem:earliestEdge-unique-proper-clique")
$`\mathrm{f_{ee}}(x)` is by definition an earliest neighbor of $`x`. Two earliest edges at $`x`
have the same time, so properness makes the earliest neighbor unique.
:::

:::lemma_ "lem:neighbor-fn-injective" (uses := "def:neighbor-functions, def:two-hop-dismountable, lem:vplus-vminus-not-neighbors") (lean := "TemporalGraph.Subgraph.earliestNeighborFn_injOn, TemporalGraph.Subgraph.latestNeighborFn_injOn")
*Neighbor functions are injective outside two-hop dismountability.* Let $`H` be a finite,
nontrivial, simple, symmetric clique that is not two-hop dismountable. Then $`\mathrm{f_{ee}}` is
injective on $`V^+(H)` and $`\mathrm{f_{le}}` is injective on $`V^-(H)`.
:::

:::proof "lem:neighbor-fn-injective"
If $`\mathrm{f_{ee}}(x) = \mathrm{f_{ee}}(y) = z` for $`x \neq y` in $`V^+`, then $`z` is an
earliest neighbor of both ({bpref "lem:neighbor-fn-eq"}[]), contradicting
{bpref "lem:vplus-vminus-not-neighbors"}[]. The case of $`\mathrm{f_{le}}` is dual.
:::

:::lemma_ "lem:card-bounds" (uses := "lem:neighbor-fn-injective") (lean := "TemporalGraph.Subgraph.vplus_card_le_vminus_card, TemporalGraph.Subgraph.vminus_card_le_vplus_card, TemporalGraph.Subgraph.vminus_card_eq_vplus_card")
*Cardinality bounds from injectivity — SAND Corollary 3.3 (3).* For a finite, nontrivial, simple,
symmetric clique $`H` that is not two-hop dismountable:
$$`|V^+(H)| \le |V^-(H)| \quad \text{and} \quad |V^-(H)| \le |V^+(H)|`
so the cardinalities are equal: $`|V^-(H)| = |V^+(H)|`.
:::

:::proof "lem:card-bounds"
An injective map from $`V^+` into $`V^-` gives $`|V^+| \le |V^-|`, and dually.
:::

:::theorem "thm:neighbor-fn-bijective" (uses := "lem:neighbor-fn-injective, lem:card-bounds") (lean := "TemporalGraph.Subgraph.earliestNeighborFn_mapsTo, TemporalGraph.Subgraph.latestNeighborFn_mapsTo, TemporalGraph.Subgraph.earliestNeighborFn_bijOn, TemporalGraph.Subgraph.latestNeighborFn_bijOn")
*Neighbor functions are bijections — SAND Corollary 3.3.* When $`H` is a finite, nontrivial,
simple, symmetric clique that is not two-hop dismountable, both $`\mathrm{f_{ee}}` and
$`\mathrm{f_{le}}` are bijections between the sets $`V^+(H)` and $`V^-(H)` (`Set.BijOn`, in Lean onto `some '' H.vminus`,
resp. `some '' H.vplus`, as the functions are `Option`-valued):
$`\mathrm{f_{ee}}` maps $`V^+(H)` into $`V^-(H)` and $`\mathrm{f_{le}}` maps $`V^-(H)` into
$`V^+(H)` (`Set.MapsTo`), and both maps are injective (Lemma above), hence bijective by the
cardinality equality.
:::

:::proof "thm:neighbor-fn-bijective"
$`\mathrm{f_{ee}}` maps $`V^+` into $`V^-` (an earliest neighbor lies in $`V^-`) and is injective
there. Its image has $`|V^+| = |V^-|` elements, so, $`V^-` being finite, the image is all of
$`V^-`. The argument for $`\mathrm{f_{le}}` is dual.
:::

:::lemma_ "lem:vminus-vplus-matchings" (uses := "thm:neighbor-fn-bijective, def:vminus-vplus-vzero, def:earliest-latest-neighbor") (lean := "TemporalGraph.Subgraph.existsUnique_vplus_earliestEdge, TemporalGraph.Subgraph.existsUnique_vminus_latestEdge")
*Perfect matchings between $`V^-` and $`V^+` — SAND Corollary 3.3 (1)–(2).* Let $`H` be a
finite, nontrivial, simple, proper, symmetric clique that is not two-hop dismountable. The
earliest/latest-edge structure gives a perfect matching in each direction: every vertex
$`x \in V^-(H)` has a unique pair $`(y, n) \in V^+(H) \times \mathbb{N}` with $`y`'s earliest edge
to $`x` at time $`n`; dually, every vertex $`x \in V^+(H)` has a unique pair
$`(y, n) \in V^-(H) \times \mathbb{N}` with $`y`'s latest edge to $`x` at time $`n`.
:::

:::proof "lem:vminus-vplus-matchings"
Let $`x \in V^-`. Surjectivity of $`\mathrm{f_{ee}}` gives $`y \in V^+` whose earliest neighbor
is $`x`, hence an earliest edge $`(y,x,n)`. If $`(z,m)` is another such pair, injectivity gives
$`z = y`, and simplicity gives $`m = n`. The statement for $`V^+` and latest edges is dual.
:::

:::lemma_ "lem:reciprocity" (uses := "def:two-hop-dismountable, def:vminus-vplus-vzero, def:earliest-latest-neighbor, def:is-symm-loopless") (lean := "TemporalGraph.Subgraph.earliestEdge_reciprocity, TemporalGraph.Subgraph.latestEdge_reciprocity")
*Reciprocity — SAND Lemma 3.5.* Let $`H` be a symmetric clique that is not $`\{1,2\}`-hop
dismountable.

* If $`(v,u,n)` is the earliest edge of $`v`, then every edge from $`u` to a vertex
  $`w \in V^+(H)` occurs at a time $`j \ge n`.
* If $`(u,v,n)` is the latest edge of $`u`, then every edge from $`v` to a vertex
  $`w \in V^-(H)` occurs at a time $`j \le n`.
:::

:::proof "lem:reciprocity"
Suppose an edge $`uw` at a time $`j < n` with $`w \in V^+`. Then $`w \neq v` (the earliest edge of
$`v` has the minimal time $`n`) and $`w` is reached from $`v`'s earliest edge in two hops,
through $`u` at a time $`j \le n`; it is also a latest neighbor since $`w \in V^+`. So $`H` is
two-hop dismountable at $`w`, a contradiction. The second statement is dual, with $`w \in V^-` and
the latest edge of $`u`.
:::

:::corollary "cor:biclique-of-not-two-hop" (uses := "lem:dismountable-iff-intersection, lem:twoHop-of-dismountable, lem:partition-finite, def:is-biclique, def:between") (lean := "TemporalGraph.Subgraph.biclique_of_not_twoHopDismountable")
*Bi-clique between $`V^-` and $`V^+` — SAND Corollary 4.1.* Let $`H` be a clique that is not $`\{1,2\}`-hop dismountable. The restriction
$`H.\mathrm{between}\ V^-(H)\ V^+(H)` of $`H` to the arcs between $`V^-` and $`V^+` is a temporal
bi-clique on $`(V^-(H), V^+(H))`.
:::

:::proof "cor:biclique-of-not-two-hop"
$`V^-` and $`V^+` are disjoint, since a common vertex would make $`H` dismountable
({bpref "lem:dismountable-iff-intersection"}[]), hence two-hop dismountable
({bpref "lem:twoHop-of-dismountable"}[]); both are contained in $`\mathrm{Verts}(H)`
({bpref "lem:partition-finite"}[]), which is a clique. Restricting a clique to the arcs between
two disjoint parts yields a bi-clique on these parts.
:::

:::lemma_ "lem:between-tc" (uses := "cor:biclique-of-not-two-hop, lem:vzero-empty, lem:vminus-vplus-matchings, lem:reachable-of-earliestEdge, lem:reachable-of-latestEdge") (lean := "TemporalGraph.Subgraph.temporallyConnectedSubgraph_between_of_not_twoHopDismountable")
*The bi-clique is temporally connected — SAND remark after Corollary 4.1.* Let $`H` be a finite,
nontrivial, simple, proper, symmetric clique that is not $`\{1,2\}`-hop dismountable. Then
$`H.\mathrm{between}\ V^-(H)\ V^+(H)` is temporally connected on $`\mathrm{Verts}(H)`.
:::

:::proof "lem:between-tc"
Since $`V^0 = \emptyset` ({bpref "lem:vzero-empty"}[]), every vertex lies in $`V^-` or $`V^+`. A
vertex of $`V^-` and a vertex of $`V^+` are joined by an edge of the bi-clique
({bpref "cor:biclique-of-not-two-hop"}[]), in both directions. For $`x, y \in V^-`: by
{bpref "lem:vminus-vplus-matchings"}[], $`x` is the endpoint of the earliest edge of some
$`p \in V^+`, which is still its earliest edge in the bi-clique; $`y` reaches $`p` directly, and
{bpref "lem:reachable-of-earliestEdge"}[] gives that $`y` reaches $`x`. The case of two vertices
of $`V^+` is dual, with latest edges.
:::

# Dismounting and mounting operations

:::definition "def:dismount-mount" (uses := "def:sub-temporal-graph, def:vminus-vplus-vzero") (lean := "TemporalGraph.Subgraph.dismount, TemporalGraph.Subgraph.mount, TemporalGraph.Subgraph.twoHopMount")
*Dismount / mount.* $`H.\mathrm{dismount}(x)` removes vertex $`x` from $`H` (special case of
deletion). $`H.\mathrm{mount}(x, y, z, n, m)` reconstructs a subgraph by adding $`x` back with
edges $`y \to x` at time $`n` and $`z \to x` at time $`m`.
$`H.\mathrm{twoHopMount}(x, y', y, z', z, n', n, m', m)` adds $`x` along a two-hop path:
$`x \to y'` at $`n'`, $`y' \to y` at $`n`, and symmetrically for $`z`.
:::

:::lemma_ "lem:dismount-clique" (uses := "def:dismount-mount") (lean := "TemporalGraph.Subgraph.dismount_clique")
*Dismounted cliques remain cliques.* Dismounting a vertex from a clique yields a clique.
:::

:::proof "lem:dismount-clique"
Two distinct vertices of $`\mathrm{Verts}(H) \setminus \{x\}` are joined in $`H`, and the edge
survives in the induced subgraph since neither endpoint is $`x`.
:::

:::lemma_ "lem:mount-size" (uses := "def:dismount-mount, def:arcset-edgeset") (lean := "TemporalGraph.Subgraph.mount_size, TemporalGraph.Subgraph.ncard_edgeSet_mount_le, TemporalGraph.Subgraph.twoHopMount_size, TemporalGraph.Subgraph.ncard_edgeSet_twoHopMount_le")
*Mount operations increase edge count.* In a symmetric ambient graph, mounting a single vertex
adds at most 2 edges to the edge set; two-hop mounting adds at most 4 edges.
:::

:::proof "lem:mount-size"
The edge set of the mounted graph is that of $`H` plus two pairs (four for the two-hop mount), and
`Set.ncard` of a union is at most the sum of the cardinalities.
:::

:::theorem "thm:dismountability" (uses := "def:dismount-mount, def:subgraph-reachable-tc-spannerOf, def:sub-spanning-clique, def:earliest-latest-neighbor, def:two-hop-dismountable") (lean := "TemporalGraph.Subgraph.dismountability, TemporalGraph.Subgraph.twoHopDismountability")
*Dismount/mount preserves spanners — SAND Theorem 2.1 (1-hop), §2.1 (2-hop).* Let the ambient
graph $`G` be symmetric, let $`H` be a symmetric clique sub-temporal-graph of $`G`
and $`x \in \mathrm{Verts}(H)`, and let $`H'` be a symmetric sub-temporal-graph of $`G` that is a
spanner of $`H.\mathrm{dismount}(x)` ({bpref "def:subgraph-reachable-tc-spannerOf"}[]).

* (1-hop) Let $`y, z \in \mathrm{Verts}(H')` with $`yx` an edge of $`G` at time $`n` and $`zx` an
  edge of $`G` at time $`m`. If $`(y,x,n)` is the earliest edge of $`y` in $`H` and $`(z,x,m)` is
  the latest edge of $`z` in $`H`, then $`H'.\mathrm{mount}(x,y,z,n,m)` is a spanner of $`H`.
* ($`2`-hop) Let $`y, y', z, z' \in \mathrm{Verts}(H')`, with edges $`xy'` at $`n'`, $`y'y` at
  $`n`, $`xz'` at $`m'` and $`z'z` at $`m` in $`G`. If $`(y,y',n)` is the earliest edge of $`y` in
  $`H` with $`n' \le n` and $`xy'` an edge of $`H` at $`n'`, and $`(z,z',m)` is the latest edge of
  $`z` in $`H` with $`m \le m'` and $`xz'` an edge of $`H` at $`m'`, then
  $`H'.\mathrm{twoHopMount}(x,y',y,z',z,n',n,m',m)` is a spanner of $`H`.
:::

:::proof "thm:dismountability" (uses := "lem:dismount-clique, lem:clique-temporally-connected, lem:reachable-of-earliestEdge, lem:reachable-of-latestEdge")
The mounted graph has the vertex set of $`H` and is below $`H`: $`H'` is below $`H - x`, and the
added edges are edges of $`H`. It is temporally connected: $`H - x` is a clique, hence temporally
connected, so $`H'` is temporally connected on $`\mathrm{Verts}(H) \setminus \{x\}` as a spanner
of it; the new vertex $`x` reaches everything $`y` reaches (through the earliest edge of $`y`, or
in two hops with $`y'`, {bpref "lem:reachable-of-earliestEdge"}[]) and is reached from everything
that reaches $`z` ({bpref "lem:reachable-of-latestEdge"}[]). A temporally connected spanning
subgraph preserves every reachability of $`H`.
:::

# One-sided dismountability (SAND 2025, §4.1)

The one-sided strategy is due to Angrick, Bals, Friedrich, Gawendowicz, Hastrich, Klodt, Lenzner,
Schmidt, Skretas and Wells (_How to Reduce Temporal Cliques to Find Sparse Spanners_, ESA 2024),
as recalled in SAND 2025, §4.1: spanners are only required to connect a source part to a target
part of a temporal bi-clique, and a target vertex sharing its latest neighbor in the source with
another target can be dismounted at the cost of two edges.

:::definition "def:spanner-from-to" (uses := "def:sub-temporal-graph, def:reachable") (lean := "TemporalGraph.Subgraph.IsSpannerFromTo, TemporalGraph.OneSidedDismountable, TemporalGraph.Subgraph.oneSidedMount")
*One-sided spanner.* $`H'` is a _one-sided spanner_ of $`H` from $`S` to $`T` if $`H' \le H` and
every vertex of $`S` reaches in $`H'` every vertex of $`T` it reaches in $`H`. A target vertex
$`x \in T` is _one-sided dismountable_ when another target $`x'` has a latest edge to some
$`y \in S`, at time $`n`, and $`y` is joined to $`x` at a time $`m \ge n`: $`x` receives through
$`x' \to y \to x` everything $`x'` receives from $`S`, and it is put back with the two edges
$`yx'` and $`yx`.
:::

:::lemma_ "lem:spanner-from-to-sup" (uses := "def:spanner-from-to") (lean := "TemporalGraph.Subgraph.IsSpannerFromTo.sup")
*Split.* If $`H_1` and $`H_2` are one-sided spanners of $`H` from $`S_1` and from $`S_2` to the
same target $`T`, then $`H_1 \sqcup H_2` is a one-sided spanner of $`H` from $`S_1 \cup S_2` to
$`T`.
:::

:::proof "lem:spanner-from-to-sup" (uses := "def:spanner-from-to")
The union is below $`H`. A walk in $`H_1` or in $`H_2` is also a walk in the union (monotonicity
of reachability), and a vertex of $`S_1 \cup S_2` lies in $`S_1` or in $`S_2`.
:::

:::theorem "thm:tc-of-spanner-from-to" (uses := "def:spanner-from-to, lem:vminus-vplus-matchings, lem:vzero-empty, cor:biclique-of-not-two-hop") (lean := "TemporalGraph.temporallyConnected_of_reachable_of_matchings, TemporalGraph.Subgraph.temporallyConnected_of_isSpannerFromTo")
*Temporal connectivity from the matchings.* In a symmetric temporal graph, if every vertex of
$`T` is the endpoint of the earliest edge of a vertex of $`S`, every vertex of $`S` the endpoint
of the latest edge of a vertex of $`T`, and every vertex of $`S` reaches every vertex of $`T`,
then $`S \cup T` is temporally connected. In particular, let $`H` be a finite, nontrivial,
simple, proper, symmetric clique that is not $`\{1,2\}`-hop dismountable, and $`S` a symmetric
one-sided spanner from $`V^+` to $`V^-` of the bi-clique of {bpref "cor:biclique-of-not-two-hop"}[]
that contains the earliest edges of the vertices of $`V^+` and the latest edges of the vertices of
$`V^-` (the matchings $`M^-` and $`M^+`). Then $`S` is temporally connected on
$`\mathrm{Verts}(H)`.
:::

:::proof "thm:tc-of-spanner-from-to" (uses := "lem:reachable-of-earliestEdge, lem:reachable-of-latestEdge")
Distinguish where the two vertices lie. From $`s \in S` to $`t \in T` it is the hypothesis. From
$`s` to $`s' \in S`: reach a vertex $`b \in T` whose latest edge ends at $`s'`, and extend along
it ({bpref "lem:reachable-of-latestEdge"}[]). From $`t \in T` to $`t'`: leave along the earliest
edge into $`t` towards its matched $`v \in S`, which reaches $`t'`
({bpref "lem:reachable-of-earliestEdge"}[]). The case $`T \to S` combines the two. For the
spanner version, $`V^0 = \emptyset` ({bpref "lem:vzero-empty"}[]), so
$`\mathrm{Verts}(H) = V^+ \cup V^-`; the matchings of {bpref "lem:vminus-vplus-matchings"}[] are in
$`S` and are still earliest/latest edges there since $`S \le H`; and $`V^+ \to V^-` reachability
is a direct edge of the bi-clique, kept by the one-sided spanner.
:::

:::theorem "thm:one-sided-dismountability" (uses := "def:spanner-from-to") (lean := "TemporalGraph.Subgraph.oneSidedDismountability, TemporalGraph.Subgraph.oneSidedMount_size, TemporalGraph.Subgraph.ncard_edgeSet_oneSidedMount_le")
*One-sided dismounting.* Let $`G` and $`H` be symmetric and $`H` a bi-clique on $`(S, T)`. Let
$`x \in T` be one-sided dismountable through $`x' \in T \setminus\{x\}` and $`y \in S`
($`(x',y,n)` is the latest edge of $`x'` in $`H`, $`yx` is an edge of $`H` at a time $`m \ge n`),
and let $`H'` be a symmetric one-sided spanner from $`S` to $`T \setminus \{x\}` of the bi-clique
without $`x`, containing $`x'` and $`y`. Extended by the two edges $`yx'` and $`yx`, $`H'` is a
one-sided spanner of $`H` from $`S` to $`T`; it has at most two more edges.
:::

:::proof "thm:one-sided-dismountability" (uses := "lem:reachable-of-latestEdge")
The mounted graph is below $`H`. For $`z \in S` and $`w \in T \setminus \{x\}`, $`z` reaches $`w`
in the bi-clique without $`x` by a direct edge, hence in $`H'`, hence in the mounted graph. For
$`w = x`: $`z` reaches $`x'` this way, and extends along the latest edge $`(x', y, n)` then the
edge $`yx` at $`m \ge n` ({bpref "lem:reachable-of-latestEdge"}[]). The count is that of two
added edges.
:::

:::lemma_ "lem:exists-one-sided-dismountable" (uses := "def:spanner-from-to") (lean := "TemporalGraph.Subgraph.exists_latestEdge_of_isBicliqueWith, TemporalGraph.Subgraph.exists_oneSidedDismountable_of_ncard_lt")
*Pigeonhole.* In a finite, simple, symmetric bi-clique on $`(S, T)` with $`S` nonempty and
$`|S| < |T|`, two vertices of $`T` share their latest neighbor in $`S`, so some vertex of $`T` is
one-sided dismountable.
:::

:::proof "lem:exists-one-sided-dismountable"
Every $`x \in T` has a latest edge, towards some $`f(x) \in S` (finiteness and simplicity). Since
$`|S| < |T|`, the pigeonhole principle gives $`a \neq b` in $`T` with $`f(a) = f(b) = y`, at
times $`n_a, n_b`. If $`n_a \le n_b` then $`b` is one-sided dismountable through $`a` and $`y`
(the edge $`yb` occurs at $`n_b \ge n_a`); otherwise $`a` is dismountable through $`b`.
:::

:::lemma_ "lem:spanner-from-to-split" (uses := "lem:spanner-from-to-sup, lem:isBicliqueWith-induce-deleteVerts, lem:reachable-of-isBicliqueWith") (lean := "TemporalGraph.Subgraph.IsSpannerFromTo.of_le, TemporalGraph.Subgraph.isSpannerFromTo_sup_of_induce")
*Split, full step.* For $`S_1, S_2 \subseteq S`, and a bi-clique $`H` on $`(S, T)` with
$`S \cup T \subseteq \mathrm{Verts}(H)`, the restrictions of $`H` to
$`S_i \cup T` are bi-cliques on $`(S_i, T)`, and one-sided spanners of these two subproblems
combine, by union, into a one-sided spanner of the bi-clique from $`S_1 \cup S_2` to $`T`.
:::

:::proof "lem:spanner-from-to-split"
For each $`i`, $`H.\mathrm{induce}(S_i \cup T)` is below $`H` and is a bi-clique on $`(S_i, T)`
({bpref "lem:isBicliqueWith-induce-deleteVerts"}[]), so every vertex of $`S_i` reaches every
vertex of $`T` in it ({bpref "lem:reachable-of-isBicliqueWith"}[]). A one-sided spanner of the
induced subgraph is therefore a one-sided spanner of $`H` from $`S_i` to $`T`; conclude with
{bpref "lem:spanner-from-to-sup"}[].
:::

:::lemma_ "lem:exists-ncard-halves" (lean := "Set.exists_subset_ncard_halves")
*Splitting a set into halves.* Any set $`S` has a subset $`S_1 \subseteq S` with
$`|S_1| = \lceil |S|/2 \rceil` and $`|S \setminus S_1| = \lfloor |S|/2 \rfloor`, unconditionally
(an infinite $`S` has `Set.ncard` $`0`, and the statement holds trivially with
$`S_1 = \emptyset`). Combined with {bpref "lem:spanner-from-to-split"}[] (taking
$`S_1, S_2 = S_1, S \setminus S_1`), this is the recursive splitting step of the one-sided
dismounting strategy, SAND 2025 §4.1.
:::

:::proof "lem:exists-ncard-halves"
If $`S` is finite, pick a subset of the required size and compute the cardinality of the
difference; if $`S` is infinite, $`\emptyset` works as all cardinalities are $`0`.
:::

:::definition "def:spanner-bound" (uses := "def:spanner-from-to") (lean := "TemporalGraph.Subgraph.spannerBound")
*Spanner-size recurrence — SAND §4.1.* $`\mathrm{spannerBound}(n)` is $`1` for $`n \le 1`, and
$`\mathrm{spannerBound}(\lceil n/2 \rceil) + \mathrm{spannerBound}(\lfloor n/2 \rfloor) + 2n` for
$`n \ge 2`: split the source in halves ({bpref "lem:exists-ncard-halves"}[]), and in each half
dismount the other half's targets ({bpref "thm:one-sided-dismountability"}[]) at two edges each.
:::

:::lemma_ "lem:spanner-bound-closed-form" (uses := "def:spanner-bound") (lean := "TemporalGraph.Subgraph.spannerBound_le")
*Closed form.* $`\mathrm{spannerBound}(n) \le 2n \lceil \log_2 n \rceil + n` for $`n \ge 1`.
:::

:::proof "lem:spanner-bound-closed-form"
Strong induction using the recurrence: both halves have a ceiling logarithm at most
$`\lceil \log_2 n\rceil - 1` (halving with a ceiling lowers $`\lceil\log_2\rceil` by at least one
for $`n \ge 2`), and the two halves sum to $`n`; the inequality then follows by arithmetic.
:::

:::theorem "thm:spanner-bound-isBigO" (uses := "lem:spanner-bound-closed-form") (lean := "TemporalGraph.Subgraph.spannerBound_isBigO")
*$`\mathrm{spannerBound}` is $`O(n \log n)`.* $`n \mapsto \mathrm{spannerBound}(n)` is
$`O(n \log n)`.
:::

:::proof "thm:spanner-bound-isBigO" (uses := "lem:spanner-bound-closed-form")
By the closed form and $`\lceil \log_2 n\rceil \le \log_2 n + 1`,
$`\mathrm{spannerBound}(n) \le 2n(\log_2 n + 1) + n \le 5 n \log_2 n` for $`n \ge 2`, since
$`1 \le \log_2 n`.
:::

:::theorem "thm:exists-spanner-from-to-ncard-le" (uses := "def:spanner-bound, lem:exists-one-sided-dismountable, thm:one-sided-dismountability, lem:spanner-from-to-split, lem:exists-ncard-halves") (lean := "TemporalGraph.Subgraph.exists_isSpannerFromTo_of_singleton, TemporalGraph.Subgraph.exists_isSpannerFromTo_ncard_le")
*One-sided spanner bound — SAND §4.1.* Let $`G` and $`H` be symmetric, and $`H` a finite simple
temporal bi-clique on a nonempty source $`S` and a target $`T` with $`|S| \le |T|`. Then $`H`
admits a symmetric one-sided spanner from $`S` to $`T` with at most
$`2(|T| - |S|) + \mathrm{spannerBound}(|S|)` edges.
:::

:::proof "thm:exists-spanner-from-to-ncard-le"
Strong induction on $`|S| + |T|`, dismounting one target at a time while $`|S| < |T|`
({bpref "lem:exists-one-sided-dismountable"}[], {bpref "thm:one-sided-dismountability"}[]), then,
once $`|S| = |T|`, either taking the single bi-clique edge if $`|S| = |T| = 1` (base case
`exists_isSpannerFromTo_of_singleton`), or splitting $`S` in halves and recursing on each half
({bpref "lem:exists-ncard-halves"}[], {bpref "lem:spanner-from-to-split"}[]); the edge count
follows the recurrence defining $`\mathrm{spannerBound}`.
:::

:::definition "def:one-sided-spanner-bound" (uses := "def:spanner-from-to") (lean := "TemporalGraph.Subgraph.IsOneSidedSpannerBound")
*One-sided spanner bound.* $`f` _bounds the one-sided spanners of temporal bi-cliques_ (Angrick et
al.'s $`\mathcal{D}(n) \le f(n)`, SAND 2025 §4.1) if every finite simple temporal bi-clique, with
symmetric ambient graph and bi-clique, and with balanced nonempty parts of size $`n`, admits a
symmetric one-sided spanner from the source to the target with at most $`f(n)` edges.
:::

:::lemma_ "lem:one-sided-spanner-bound-spannerBound" (uses := "def:spanner-bound, def:one-sided-spanner-bound, thm:exists-spanner-from-to-ncard-le") (lean := "TemporalGraph.Subgraph.isOneSidedSpannerBound_spannerBound")
*$`\mathrm{spannerBound}` is a one-sided spanner bound.* $`\mathrm{spannerBound}` bounds the
one-sided spanners of temporal bi-cliques.
:::

:::proof "lem:one-sided-spanner-bound-spannerBound"
Apply {bpref "thm:exists-spanner-from-to-ncard-le"}[] with $`|S| = |T|`, so the term
$`2(|T|-|S|)` vanishes.
:::

:::theorem "thm:exists-isBigO-one-sided-spanner-bound" (uses := "thm:spanner-bound-isBigO, lem:one-sided-spanner-bound-spannerBound") (lean := "TemporalGraph.Subgraph.exists_isBigO_isOneSidedSpannerBound")
*$`O(n \log n)` one-sided spanners — SAND §4.1.* Temporal bi-cliques admit one-sided spanners of
size $`O(n \log n)`: there is a one-sided spanner bound that is $`O(n \log n)`.
:::

:::proof "thm:exists-isBigO-one-sided-spanner-bound"
Take $`f = \mathrm{spannerBound}`.
:::

# Spanners of temporal cliques (SAND 2025, §4.1)

:::theorem "thm:spanner-of-two-hop-dismountable" (uses := "def:two-hop-dismountable, def:dismount-mount, thm:dismountability") (lean := "TemporalGraph.Subgraph.exists_isSpannerOf_of_twoHopDismountable")
*Mounting back, mixed $`\{1,2\}`-hop case.* Let $`G` be symmetric and loopless. A symmetric
$`\{1,2\}`-hop dismountable clique $`H` has a vertex $`x` such that every symmetric spanner $`H'`
of $`H - x` extends to a symmetric spanner of $`H` with at most $`4` more edges. On each side of
$`x` (earliest and latest) the witness of dismountability gives a set of $`1` or $`2` edges,
which are added at once. The four combinations of $`1` or $`2` hops are thus handled uniformly,
and only the count takes the worst case.
:::

:::proof "thm:spanner-of-two-hop-dismountable" (uses := "lem:reachable-of-earliestEdge, lem:reachable-of-latestEdge")
Each side of the two-hop condition yields a set of at most two edges of $`H` (the edge $`yx`, or
the two edges $`yz` and $`zx`) such that, in any symmetric $`K` between these edges and $`H`,
everything reachable from $`y` is reachable from $`x` ({bpref "lem:reachable-of-earliestEdge"}[]);
dually on the latest side. Given a spanner $`H'` of $`H - x`, take
$`K = H' \sqcup \mathrm{fromEdgeSet}(E_o \cup E_i)`. It is below $`H`, has the vertex set of
$`H` and at most four more edges. Pairs not involving $`x` are reachable in $`H'` ($`H - x` is a
clique); from $`x`, go as $`y` does, and to $`x`, as one goes to $`z`.
:::

:::theorem "thm:clique-induction" (uses := "thm:spanner-of-two-hop-dismountable, def:spanner") (lean := "TemporalGraph.Subgraph.exists_isSpannerOf_ncard_le_of_forall_not_twoHopDismountable")
*Generic clique induction — SAND Theorem 2.1 and §2.1.* Let $`G` be symmetric and loopless, and
$`f : \mathbb{N} \to \mathbb{N}` with $`f(n) + 4 \le f(n + 1)` for all $`n`. If every finite,
nontrivial, simple, proper, symmetric clique that is not $`\{1,2\}`-hop dismountable has a
symmetric spanner with at most $`f(n)` edges, $`n` its number of vertices, then so does every
finite, simple, proper, symmetric clique.
:::

:::proof "thm:clique-induction" (uses := "lem:dismount-clique, lem:mount-size")
By strong induction on $`n`; with at most one vertex, $`H` has no edge and is its own spanner. If
$`H` is $`\{1,2\}`-hop dismountable, dismount a vertex ($`H - x` is again a clique,
{bpref "lem:dismount-clique"}[]), recurse, and mount it back with at most $`4` edges
({bpref "thm:spanner-of-two-hop-dismountable"}[]): $`f(n - 1) + 4 \le f(n)`. Otherwise the
hypothesis applies.

This induction is the proof engine of the library. It isolates what the two spanner bounds share,
the dismountable case, and leaves to each bound only the non-dismountable case and the inequality
$`f(n) + 4 \le f(n + 1)`. The $`O(n \log n)` bound below
({bpref "thm:clique-spanner-ncard-le"}[]) and the linear bound
({bpref "thm:clique-spanner-seven-mul"}[]) are two instances of it.
:::

:::theorem "thm:spanner-of-not-two-hop-dismountable" (uses := "lem:vminus-vplus-matchings, lem:vzero-empty, cor:biclique-of-not-two-hop, thm:tc-of-spanner-from-to, thm:exists-spanner-from-to-ncard-le") (lean := "TemporalGraph.Subgraph.exists_isSpannerOf_of_not_twoHopDismountable")
*Spanner of a non-dismountable clique.* Let $`G` be symmetric and loopless. A finite, nontrivial,
simple, proper, symmetric temporal clique $`H` that is not $`\{1,2\}`-hop dismountable has a
symmetric spanner with at most $`\mathrm{spannerBound}(|V^+|) + |V^+| + |V^-|` edges. It is the
union of a one-sided spanner from $`V^+` to $`V^-` of the bi-clique between $`V^-` and $`V^+` and
of the matchings $`M^-` and $`M^+`.
:::

:::proof "thm:spanner-of-not-two-hop-dismountable"
Here $`V^0 = \emptyset` and $`|V^+| = |V^-|`, and the bi-clique between $`V^-` and $`V^+` has a
one-sided spanner $`S` from $`V^+` to $`V^-` with at most $`\mathrm{spannerBound}(|V^+|)` edges
({bpref "thm:exists-spanner-from-to-ncard-le"}[]). Choose the matchings $`M^-` (earliest edges
into $`V^-`) and $`M^+` (latest edges into $`V^+`) of {bpref "lem:vminus-vplus-matchings"}[].
Then $`S \sqcup M^- \sqcup M^+` is below $`H`, spans $`\mathrm{Verts}(H) = V^- \cup V^+`, has the
stated number of edges, and is temporally connected ({bpref "thm:tc-of-spanner-from-to"}[]),
which is enough since $`H` is a clique.
:::

:::theorem "thm:clique-spanner-ncard-le" (uses := "thm:clique-induction, thm:spanner-of-not-two-hop-dismountable, lem:spanner-bound-closed-form") (lean := "TemporalGraph.Subgraph.exists_isSpannerOf_ncard_le")
*Spanners of temporal cliques — SAND §4.1.* Let $`G` be symmetric and loopless and $`H` a finite,
simple, proper, symmetric temporal clique on $`n` vertices. Then $`H` admits a symmetric spanner
with at most $`2n\lceil\log_2 n\rceil + 4n` edges.
:::

:::proof "thm:clique-spanner-ncard-le" (uses := "lem:vzero-empty, lem:card-bounds")
An instance of {bpref "thm:clique-induction"}[] with $`f(n) = 2n\lceil\log_2 n\rceil + 4n`. Two
obligations remain.

* The step $`f(n) + 4 \le f(n + 1)` follows from the monotonicity of $`\lceil\log_2 n\rceil`.
* For a clique that is not $`\{1,2\}`-hop dismountable, $`V^0 = \emptyset`
  ({bpref "lem:vzero-empty"}[]) and $`|V^-| = |V^+| = k` ({bpref "lem:card-bounds"}[]), so
  $`n = 2k`. {bpref "thm:spanner-of-not-two-hop-dismountable"}[] gives a spanner with at most
  $`\mathrm{spannerBound}(k) + 2k` edges, and the closed form
  $`\mathrm{spannerBound}(k) \le 2k\lceil\log_2 k\rceil + k`
  ({bpref "lem:spanner-bound-closed-form"}[]) bounds it by $`f(2k)`.
:::
