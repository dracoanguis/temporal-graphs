import Verso
import VersoManual
import VersoBlueprint
import Blueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Sub-temporal-graphs and spanners" =>

%%%
tag := "chap:spanners"
%%%

Formalized in `TemporalGraph/Subgraph.lean` (general subgraph theory) and
`TemporalGraph/Connectivity/Subgraph.lean` (reachability and spanners at the subgraph level).

:::definition "def:sub-temporal-graph" (uses := "def:temporal-graph") (lean := "TemporalGraph.Subgraph")
*Sub-temporal-graph.* A _sub-temporal-graph_ $`H` of a temporal graph $`G` is a choice of vertex
subset $`\mathrm{Verts}(H) \subseteq V` together with an edge relation on it that is compatible
with (a restriction of) $`G`'s edges. In the library, $`H` literally _is_ a temporal graph on
$`V` (extending {bpref "def:temporal-graph"}[]) together with $`\mathrm{Verts}(H)` and proofs
that every one of its edges is one of $`G`'s and has both endpoints in $`\mathrm{Verts}(H)`; in
particular $`H` need not be symmetric even when $`G` is.
:::

:::definition "def:sub-spanning-clique" (uses := "def:sub-temporal-graph, def:is-simple-clique") (lean := "TemporalGraph.Subgraph.IsSpanning, TemporalGraph.Subgraph.IsCliqueSubgraph")
*Spanning, clique sub-temporal-graph.* $`H` _is spanning_ in $`G` if $`\mathrm{Verts}(H) = V`.
$`H` _is a clique_ (or a _clique subgraph_ via `IsCliqueSubgraph`) if its vertex set
$`\mathrm{Verts}(H)` forms a clique in $`H` itself ({bpref "def:is-simple-clique"}[]): every pair
of distinct vertices of $`\mathrm{Verts}(H)` is joined by an edge of $`H` at some time.
:::

:::definition "def:subgraph-order" (uses := "def:sub-temporal-graph") (lean := "TemporalGraph.Subgraph.top_toTemporalGraph")
*Order on sub-temporal-graphs.* Sub-temporal-graphs of $`G` are ordered by inclusion:
$`H \le H'` when $`\mathrm{Verts}(H) \subseteq \mathrm{Verts}(H')` and every edge of $`H` is one
of $`H'` — the analogue, one level down, of {bpref "def:spanning-order"}[]. This makes the
sub-temporal-graphs of $`G` a bounded partial order: the bottom element $`\bot` is the empty
sub-temporal-graph, and the top element $`\top` is $`G` itself, seen as a sub-temporal-graph of
itself on all of $`V`.
:::

:::lemma_ "lem:subgraph-le-iff-edgeSet-verts" (uses := "def:subgraph-order, def:arcset-edgeset") (lean := "TemporalGraph.Subgraph.le_iff_edgeSet_and_verts")
*Order via edge sets and vertex sets.* When $`H'` is symmetric, $`H \le H'` exactly when
$`\mathrm{EdgeSet}(H) \subseteq \mathrm{EdgeSet}(H')` and
$`\mathrm{Verts}(H) \subseteq \mathrm{Verts}(H')`.
:::

:::proof "lem:subgraph-le-iff-edgeSet-verts"
($`\Rightarrow`) An arc of $`H` is an arc of $`H'`, so edges map to edges; the vertex inclusion
is part of $`H \le H'`. ($`\Leftarrow`) An arc of $`H` gives an edge of $`H`, hence an edge of
$`H'`, hence (by symmetry of $`H'`) an arc of $`H'`.
:::

:::lemma_ "lem:toTemporalGraph-le" (uses := "def:subgraph-order") (lean := "TemporalGraph.Subgraph.toTemporalGraph_le, TemporalGraph.Subgraph.toTemporalGraph_le_self")
*$`\le` is compatible with `toTemporalGraph`.* If $`H \le H'` as sub-temporal-graphs of $`G`,
then $`H.\mathrm{toTemporalGraph} \le H'.\mathrm{toTemporalGraph}`, the inherited order of
{bpref "def:spanning-order"}[]. Every sub-temporal-graph's $`\mathrm{toTemporalGraph}` is, in
particular, a spanning sub-temporal-graph of $`G` itself.
:::

:::proof "lem:toTemporalGraph-le"
Direct from the definitions: the order on sub-temporal-graphs includes the implication on
adjacencies, and every arc of $`H` is an arc of $`G` by the compatibility field.
:::

:::definition "def:subgraph-sup" (uses := "def:subgraph-order, def:arcset-edgeset") (lean := "TemporalGraph.Subgraph.sup_edgeSet")
*Union of sub-temporal-graphs.* Sub-temporal-graphs of $`G` form a `SemilatticeSup`:
$`H_1 \sqcup H_2` has vertex set $`\mathrm{Verts}(H_1) \cup \mathrm{Verts}(H_2)` and keeps an
edge of either $`H_1` or $`H_2`, and it is the least upper bound of $`H_1` and $`H_2` for the
order of {bpref "def:subgraph-order"}[]. Its edge set is the union
$`\mathrm{EdgeSet}(H_1) \cup \mathrm{EdgeSet}(H_2)`.
:::

:::definition "def:subgraph-induce-delete-add" (uses := "def:sub-temporal-graph") (lean := "TemporalGraph.Subgraph.IsInduced, TemporalGraph.Subgraph.induce, TemporalGraph.Subgraph.deleteVerts, TemporalGraph.Subgraph.addVerts")
*Induced, added, deleted sub-temporal-graphs.* $`H` _is induced_ if every $`G`-edge between two
vertices of $`H` is already an edge of $`H`. Given $`s \subseteq V`, the sub-temporal-graph
$`H[s]` _induced by $`H` on $`s`_ has vertex set $`s` and keeps exactly the edges of $`H` whose
both endpoints lie in $`s`; it is always a sub-temporal-graph of $`G`, whether or not
$`s \subseteq \mathrm{Verts}(H)`. Deleting $`s` from $`H` is $`H[\mathrm{Verts}(H) \setminus s]`;
adding $`s` to $`H` is $`H[\mathrm{Verts}(H) \cup s]` — both special cases of induction, and both
below, resp. above, $`H` in the order of {bpref "def:subgraph-order"}[].
:::

:::lemma_ "lem:subgraph-finite-induce-delete" (uses := "def:subgraph-induce-delete-add") (lean := "TemporalGraph.Subgraph.finite_induce_verts, TemporalGraph.Subgraph.deleteVerts_finite")
*Finiteness is preserved by induction and deletion.* If $`\mathrm{Verts}(H)` is finite, then so
is $`\mathrm{Verts}(H[s])` for any $`s \subseteq \mathrm{Verts}(H)` (in particular, so is
$`\mathrm{Verts}(H \setminus s)`, as an instance named `deleteVerts_finite`): both vertex sets
are subsets of $`\mathrm{Verts}(H)`.
:::

:::proof "lem:subgraph-finite-induce-delete"
Both vertex sets are subsets of the finite set $`\mathrm{Verts}(H)`.
:::

:::lemma_ "lem:subgraph-finite-edgeSet-of-simple" (uses := "def:sub-spanning-clique, def:arcset-edgeset") (lean := "TemporalGraph.Subgraph.finite_edgeSet_of_finite_simple")
*Finitely many vertices, simple: finitely many edges.* If $`H` is simple
({bpref "def:is-simple-clique"}[]) and $`\mathrm{Verts}(H)` is finite, then
$`\mathrm{EdgeSet}(H)` is finite: there is at most one time per unordered pair of vertices, and
there are finitely many such pairs.
:::

:::proof "lem:subgraph-finite-edgeSet-of-simple"
Every edge is the image of an arc $`(x,y,n)` with $`x \in \mathrm{Verts}(H)`. For each such $`x`
the incidence set is finite by simplicity (one time per neighbor), so the edge set is contained in
the image of a finite union of finite sets.
:::

:::definition "def:subgraph-addEdge" (uses := "def:sub-temporal-graph") (lean := "TemporalGraph.Subgraph.addArc, TemporalGraph.Subgraph.addEdge")
*Adding a single edge.* Given an edge $`(x,y,n)` of $`G` with $`x, y \in \mathrm{Verts}(H)`:
adding it to $`H` in one direction ($`\mathrm{addArc}`) needs no hypothesis on $`G` or $`H` at
all, and inserts only the arc $`x \to y` at time $`n`. Adding it in both directions at once
($`\mathrm{addEdge}`) needs $`G` symmetric, to find the reverse arc $`y \to x` back in $`G`.
:::

:::lemma_ "lem:subgraph-addEdge-edgeSet" (uses := "def:subgraph-addEdge, def:arcset-edgeset") (lean := "TemporalGraph.Subgraph.addEdge_edgeSet, TemporalGraph.Subgraph.ncard_edgeSet_addEdge_le")
*Adding an edge changes the edge set by one.* $`H.\mathrm{addEdge}`'s edge set is
$`\mathrm{EdgeSet}(H)` with the new pair $`(\{x,y\}, n)` inserted; in particular its `Set.ncard`
is at most $`|\mathrm{EdgeSet}(H)| + 1`, with no finiteness hypothesis needed.
:::

:::proof "lem:subgraph-addEdge-edgeSet"
Unfold $`\mathrm{addEdge}`: its adjacency is that of $`H` plus both orientations of the new arc,
so the edge set gains exactly the pair $`(\{x,y\},n)`. The cardinality bound is
`Set.ncard_insert_le`.
:::

:::lemma_ "lem:earliest-latest-edge-exists" (uses := "def:incidence-set, def:earliest-latest-neighbor") (lean := "TemporalGraph.Subgraph.exists_earliestEdge_of_incidenceSet, TemporalGraph.Subgraph.exists_latestEdge_of_incidenceSet")
*Earliest / latest edge from a finite incidence set.* If $`x`'s incidence set in $`H` is nonempty
and finite, $`x` has an earliest edge in $`H`; dually, it has a latest edge. (A nonempty finite
set of times has a minimum and a maximum.) Combined with {bpref "def:sub-spanning-clique"}[], a
finite nontrivial simple clique gives every vertex both an earliest and a latest edge — the
starting point of {ref "chap:dismountability"}[Dismountability].
:::

:::proof "lem:earliest-latest-edge-exists"
Take an element of the finite nonempty incidence set with minimal (resp. maximal) time.
:::

:::definition "def:subgraph-footprint-edgeSet" (uses := "def:sub-temporal-graph") (lean := "TemporalGraph.Subgraph.footprintEdgeSet")
*Footprint edge set.* The _footprint edge set_ of $`H` forgets time directly into unordered
pairs: it is the set of $`\{x,y\} \in \mathrm{Sym2}\,V` such that $`H.\mathrm{Adj}(x,y,n)` for
some $`n` — the same forgetful step as {bpref "def:footprint"}[]'s footprint digraph, but landing
on $`\mathrm{Sym2}\,V` (matching the shape of $`\mathrm{EdgeSet}` without the time component)
rather than on a directed graph.
:::

:::lemma_ "lem:edgeSet-footprint-bijective" (uses := "def:subgraph-footprint-edgeSet, def:arcset-edgeset, def:is-simple-clique") (lean := "TemporalGraph.Subgraph.edgeSetToFootprintEdgeSet_bijective, TemporalGraph.Subgraph.ncard_edgeSet_of_simple, TemporalGraph.Subgraph.size_of_simple")
*Edges and footprint edges are in bijection.* If $`H` is symmetric and simple, the map from
$`\mathrm{EdgeSet}(H)` to $`H`'s footprint edge set, forgetting the time component, is a
bijection: simplicity guarantees each unordered pair of $`H`-adjacent vertices carries a single
time. In particular the `Set.ncard` of $`\mathrm{EdgeSet}(H)` agrees with that of the footprint
edge set in this case, with no finiteness hypothesis needed
(`TemporalGraph.Subgraph.ncard_edgeSet_of_simple`), and so does $`H.\mathrm{size}` under a
`Fintype` instance (`TemporalGraph.Subgraph.size_of_simple`).
:::

:::proof "lem:edgeSet-footprint-bijective"
Surjective: a footprint edge comes from an arc at some time. Injective: two edges over the same
unordered pair carry times $`n` and $`m` of arcs between the same two vertices, in either
orientation (use the symmetry of $`H`), and simplicity forces $`n = m`.
:::

:::definition "def:subgraph-matching" (uses := "def:sub-temporal-graph, def:sub-spanning-clique") (lean := "TemporalGraph.Subgraph.IsMatching, TemporalGraph.Subgraph.IsPerfectMatching")
*Matching.* $`M` _is a matching_ if every vertex of $`\mathrm{Verts}(M)` has exactly one outgoing
$`M`-arc (a unique pair $`(y,n)` with $`M.\mathrm{Adj}(x,y,n)`). $`M` _is a perfect matching_ if
it is a matching and is spanning.
:::

:::definition "def:subgraph-toSubgraph-fromEdgeSet" (uses := "def:sub-temporal-graph, def:spanning-order, def:arcset-edgeset") (lean := "TemporalGraph.toSubgraph, TemporalGraph.Subgraph.fromEdgeSet")
*Building a sub-temporal-graph.* Any temporal graph $`H` with $`H \le G`
({bpref "def:spanning-order"}[]) gives a spanning sub-temporal-graph of $`G` with the same
adjacency, licensed by $`H \le G`. Dually, a set of unordered edges yields a sub-temporal-graph of
$`G`: its vertices are the endpoints of members of the set, and its adjacencies are exactly the
members of the set that already are edges of $`G` — the sub-temporal-graph analogue of
{bpref "def:from-arc-edge-set"}[]'s $`\mathrm{fromEdgeSet}`.
:::

:::definition "def:subgraph-reachable-tc-spannerOf" (uses := "def:sub-temporal-graph, def:reachable") (lean := "TemporalGraph.Subgraph.IsSpannerOf")
*Reachability and spanning for sub-temporal-graphs.* On a sub-temporal-graph $`H`, reachability
and temporal connectivity are inherited from the parent $`G` — they operate on vertices of type
$`V`. Given two sub-temporal-graphs $`H, H'` of $`G`: $`H` _is a spanner of_ $`H'` if
$`H \le H'`, they share the same vertex set, and every pair of vertices in that set that is
reachable in $`H'` remains reachable in $`H` — the relation used by the dismount/mount operations
of {ref "chap:dismountability"}[Dismountability] to transfer a spanner of a smaller clique back
onto the original one.
:::

:::lemma_ "lem:subgraph-mem-verts-of-reachable" (uses := "def:sub-temporal-graph, def:reachable") (lean := "TemporalGraph.Subgraph.mem_verts_of_reachable")
*A reachable pair of distinct vertices lies in $`H`.* If $`x \neq y` and $`y` is reachable from
$`x` in $`H`, then both $`x, y \in \mathrm{Verts}(H)`: a nonempty witnessing walk has a first and
a last edge, both of $`H`, giving each endpoint's membership.
:::

:::proof "lem:subgraph-mem-verts-of-reachable"
Since $`x \neq y` the witnessing walk is not empty, so it has a first arc leaving $`x` and a last
arc entering $`y`; the endpoints of an arc of $`H` lie in $`\mathrm{Verts}(H)`.
:::

:::definition "def:spanner" (uses := "def:sub-spanning-clique, def:reachable, def:subgraph-reachable-tc-spannerOf") (lean := "TemporalGraph.Subgraph.IsSpanner, TemporalGraph.Subgraph.IsTCSpanner")
*Temporal spanner.* A spanning sub-temporal-graph $`H` of $`G` _is a spanner_ if, for all
$`x, y \in \mathrm{Verts}(H)`, whenever $`x` reaches $`y` in $`G`, then $`x` reaches $`y` in
$`H`. $`H` _is a TC-spanner_ if it is spanning and $`\mathrm{Verts}(H)` is temporally connected
in $`H`.
:::

:::lemma_ "lem:tcspanner-iff-tc" (uses := "def:spanner") (lean := "TemporalGraph.Subgraph.exists_isTCSpanner_iff_temporallyConnectedGraph")
*TC-spanner exists iff temporally connected.* $`G` admits a TC-spanner if and only if $`G` is
temporally connected.
:::

:::proof "lem:tcspanner-iff-tc"
($`\Rightarrow`) A TC-spanner $`H` is spanning and temporally connected on
$`\mathrm{Verts}(H) = V`; reachability in $`H` transfers to $`G` by monotonicity. ($`\Leftarrow`)
The top sub-temporal-graph $`G` is spanning and has the reachability of $`G`.
:::
