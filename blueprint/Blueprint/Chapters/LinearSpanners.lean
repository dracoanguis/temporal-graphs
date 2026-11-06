import Verso
import VersoManual
import VersoBlueprint
import Blueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Linear spanners" =>

%%%
tag := "chap:linear-spanners"
%%%

Formalized in the directory `TemporalGraph/LinearSpanner/`:

* `ExtremallyMatched.lean`: extremally matched bi-cliques;
* `Reduction.lean`: dismountability in bi-cliques, Lemma 5;
* `Stars.lean`: the edge sets of the stars, Definitions 8 and 12;
* `SimpleStar.lean`: Observation 9;
* `ExtendedStar.lean`: Lemmas 13 to 16, Corollary 15;
* `Bound.lean`: Lemma 17, Theorem 18 and the bi-clique Theorem 3;
* `Clique.lean`: Theorems 20 and 2.

The supporting API is in `Basic.lean`, `Connectivity/Basic.lean`, `TemporalWalk.lean`,
`Dismountability/OneSided.lean` and `Helpers/SetCard.lean` (generic lemmas on `Set.ncard`).

The proof reuses the dismountability machinery of {ref "chap:dismountability"}[Dismountability]
rather than redoing it. The generic clique induction ({bpref "thm:clique-induction"}[]) handles
the dismountable case exactly as for the $`O(n \log n)` bound, and the non-dismountable case
reuses SAND's partition $`V^-`, $`V^+`, $`V^0`, its matchings and its reciprocity lemma
(Theorem 20 below). The genuinely new part is the bound for extremally matched bi-cliques, through
stars (Observation 9 to Theorem 18).

This chapter follows Júlia Baligács, _Temporal Cliques Admit Linear
Spanners_, arXiv:2606.05156v1 (2026) — abbreviated Baligács below, an arXiv
preprint only — which answers the question of Casteigts, Peters and
Schoeters: temporal cliques admit spanners of size $`O(n)`, improving the
$`O(n \log n)` bound of {ref "chap:main-theorem"}[Main results].
The numbering below is
that of the arXiv version v1, which uses a single counter for all statements
(Theorem 2, Lemma 5, Definition 8, Observation 9, …).

Design choices that differ from the paper.

* The paper assumes without loss of generality (§2.1) that every edge
  carries a single label and that no two edges at a vertex share a label.
  Here these are hypotheses: the graphs are simple
  (`IsSimple`, {bpref "def:is-simple-clique"}[]) and, where the
  paper uses the uniqueness of extremal edges, proper
  (`IsProper`, {bpref "def:is-proper-happy"}[]).
* No index is ever built. The paper compares positions
  $`\mathrm{pos}_v(u) < \mathrm{pos}_v(w)` in the order a vertex $`v` induces on
  its neighbors, and numbers the vertices along the order induced by a center
  (the $`s^*`- and $`t^*`-ordered labelings, Definition 7). Here
  $`\mathrm{pos}_v(u) \le \mathrm{pos}_v(w)` is the comparison of arc times
  $`\mathrm{arcTime}(v, u) \le \mathrm{arcTime}(v, w)`, and “$`j \le i`” in a
  labeling centered at $`s^*` is a comparison of the times of the edges at
  $`s^*`. A cut at index $`k` (Definition 8) is given by a threshold time $`\tau`.
* Absence is explicit. Arc times are `arcTime : Option ℕ`, and $`N_{\min}`,
  $`N_{\max}` are the functions `earliestNeighborFn`,
  `latestNeighborFn` with values in `Option V`, `none`
  standing for the absence of an edge (no junk value). A comparison is thus
  stated as “some value of $`\mathrm{arcTime}(u, v)` is at most some value of
  $`\mathrm{arcTime}(u, w)`”, false when one of the arcs is absent.
* A spanner of a bi-clique is a subgraph $`\mathrm{fromEdgeSet}(E)` of an edge
  set $`E` ({bpref "def:from-arc-edge-set"}[]), and a bi-clique spanner
  is a one-sided spanner ({bpref "def:spanner-from-to"}[]): there is no
  separate “covering” predicate.

# Preliminaries (Baligács §2.1)

:::definition "def:arc-time" (uses := "def:is-simple-clique, def:temporal-graph") (lean := "TemporalGraph.arcTime, TemporalGraph.arcTime_eq_some, TemporalGraph.arcTime_comm")
*Arc times — Baligács §§1, 2.1.* Let $`G` be a temporal graph. $`\mathrm{arcTime}(u, v)` is the
time of an arc from $`u` to $`v`, the paper's $`\lambda(\{u, v\})`, as an
`Option ℕ`: `none` when $`u` and $`v` are not adjacent, and
`some n` for the time $`n` of the arc when $`G` is simple. When $`G` is
moreover symmetric, $`\mathrm{arcTime}(u, v) = \mathrm{arcTime}(v, u)`.
:::

:::definition "def:reachable-within" (uses := "def:reachable, def:temporal-walk") (lean := "TemporalGraph.ReachableWithin, TemporalGraph.ReachableBefore, TemporalGraph.ReachableWithin.step")
*Reaching within a time window — Baligács §2.1.* $`x` _reaches $`y` within $`[a, b]`_ when some
temporal walk, possibly
empty, goes from $`x` to $`y`, leaves $`x` at a time at least $`a` and arrives at
$`y` at a time at most $`b`; $`x` _reaches $`y` before $`b`_ is the window
$`[0, b]`. A walk is extended by one arc at its end
(`ReachableWithin.step`): the paper's temporal walks, whose repeated
vertices are collapsed, are built with it one edge at a time.
:::

:::lemma_ "lem:walk-edges" (uses := "def:reachable-within, def:from-arc-edge-set") (lean := "TemporalGraph.TemporalWalk.edges, TemporalGraph.TemporalWalk.ncard_setOf_mem_edges_le, TemporalGraph.TemporalWalk.reachableBefore_fromEdgeSet")
*Edges of a walk — Baligács §2.1.* A temporal walk $`p` traverses the list $`\mathrm{edges}(p)`
of edges (an
unoriented edge together with its time), of which there are at most
$`\mathrm{length}(p)` distinct ones. If all edges of $`p` belong to a set $`E`,
the walk lives in $`\mathrm{fromEdgeSet}(E)`: the end of $`p` is reachable
from its start there, by the arrival time of $`p`.
:::

:::proof "lem:walk-edges"
By induction on the walk.
:::

# Dismountability and extremally matched bi-cliques (Baligács §2.3)

:::definition "def:source-target-dismountable" (uses := "def:is-biclique, def:earliest-latest-neighbor, def:spanner-from-to") (lean := "TemporalGraph.SourceDismountable, TemporalGraph.OneSidedDismountable")
*Dismountable sources and targets — Baligács §2.3.* Let $`G` be a temporal graph with sources
$`S` and targets $`T`. A source
$`x \in S` is _dismountable_ when another source $`x'` has its earliest
edge to a target $`y`, at time $`n`, and the edge $`yx` occurs at a time
$`m \le n`: $`x` reaches through $`x \to y \to x'` everything $`x'` reaches.
Dually, a target $`x \in T` is dismountable when another target $`x'` has its
latest edge to a source $`y`, at time $`n`, and the edge $`yx` occurs at a time
$`m \ge n`. Target dismountability is the one-sided dismountability of
{bpref "def:spanner-from-to"}[]
(`OneSidedDismountable`), and source dismountability
(`SourceDismountable`) is its mirror image.
:::

:::theorem "thm:source-dismountability" (uses := "def:source-target-dismountable, def:spanner-from-to, thm:one-sided-dismountability") (lean := "TemporalGraph.Subgraph.sourceDismountability, TemporalGraph.Subgraph.isSpannerFromTo_of_sourceDismount")
*Mounting back a source or a target — Baligács §2.3.* Let $`G` be symmetric and $`x` a
dismountable source of a symmetric bi-clique subgraph
$`H` on $`S` and $`T`. Every symmetric one-sided spanner of $`H` without $`x`,
from $`S \setminus \{x\}` to $`T`, extends to a symmetric one-sided spanner of
$`H` from $`S` to $`T` with at most two more edges, $`x'y` and $`yx`. Dually for a dismountable target
({bpref "thm:one-sided-dismountability"}[]).
:::

:::proof "thm:source-dismountability" (uses := "lem:reachable-of-earliestEdge, lem:reachable-of-latestEdge")
The earliest edge $`x'y` of $`H` stays the earliest edge at $`x'` in the smaller
graph. So $`x \to y \to x'`, at times $`m \le n`, followed by any walk from $`x'`
is a temporal walk ({bpref "lem:reachable-of-earliestEdge"}[]), and $`x`
reaches every target that $`x'` reaches. The target case appends
$`x' \to y \to x` to any walk into $`x'` ({bpref "lem:reachable-of-latestEdge"}[]).
:::

:::definition "def:extremally-matched" (uses := "def:is-biclique, def:earliest-latest-neighbor") (lean := "TemporalGraph.IsExtremallyMatched")
*Extremally matched bi-clique — Baligács §2.3.* A temporal graph $`G` is an _extremally matched_
bi-clique on sources $`S`
and targets $`T` if it is a bi-clique on $`S` and $`T` in which the earliest
edges form a perfect matching $`E_{\min}` and the latest edges a perfect
matching $`E_{\max}`: the earliest edge at any vertex of $`S \cup T` is also the
earliest edge at its other endpoint, and likewise for the latest edges.
:::

:::lemma_ "lem:extremally-matched-basic" (uses := "def:extremally-matched, def:neighbor-functions, lem:neighbor-fn-eq, def:is-proper-happy") (lean := "TemporalGraph.IsExtremallyMatched.earliestNeighborFn_eq_some_symm, TemporalGraph.IsExtremallyMatched.ncard_eq")
*Basic properties of extremally matched bi-cliques — Baligács §2.3.* In a proper extremally
matched bi-clique, if $`N_{\min}(v) = \mathrm{some}\ w`
then $`N_{\min}(w) = \mathrm{some}\ v` (and likewise for $`N_{\max}`), and
$`|S| = |T|`.
:::

:::proof "lem:extremally-matched-basic"
The earliest edge $`vw` at $`v` is also the earliest edge at $`w`, so by
uniqueness in a proper graph $`N_{\min}(v) = \mathrm{some}\ w` and
$`N_{\min}(w) = \mathrm{some}\ v`; the same holds for $`N_{\max}`. Hence
$`N_{\min}` is injective on $`S \cup T`, and it maps $`S` onto $`T`, so
$`|S| = |T|`.
:::

:::theorem "thm:extremally-matched-tc" (uses := "def:extremally-matched, def:spanner-from-to, thm:tc-of-spanner-from-to") (lean := "TemporalGraph.IsExtremallyMatched.temporallyConnected")
*Temporal connectivity of a spanner of an extremally matched bi-clique — Baligács §2.3.* Let
$`H` be an extremally matched bi-clique on $`S` and $`T`, and $`K` a
symmetric subgraph of $`H` containing the matchings $`E_{\min}` and $`E_{\max}` and in
which every source reaches every target. Then $`K` is temporally connected on
$`S \cup T`.
:::

:::proof "thm:extremally-matched-tc" (uses := "thm:tc-of-spanner-from-to")
Since $`K` contains $`E_{\min}` and $`E_{\max}`, a target reaches whatever its
$`N_{\min}` reaches and a source is reached by whatever reaches its $`N_{\max}`.
This is {bpref "thm:tc-of-spanner-from-to"}[] (SAND 2025, §4.1).
:::

:::lemma_ "lem:extremally-matched-of-not-dismountable" (uses := "def:source-target-dismountable, def:extremally-matched") (lean := "TemporalGraph.Subgraph.isExtremallyMatched_of_not_dismountable")
*No dismountable vertex — Baligács §2.3.* A finite, simple, symmetric bi-clique subgraph with
two nonempty parts and
without dismountable sources or targets is extremally matched.
:::

:::proof "lem:extremally-matched-of-not-dismountable"
Let $`v` be a source, $`w = N_{\min}(v)` and $`u = N_{\min}(w)`. If $`u \ne v`,
then $`u` is dismountable via $`(v, w)`, since its edge to $`w` is no later than
the earliest edge of $`v`; so $`N_{\min}(N_{\min}(v)) = v` and $`|S| \le |T|`.
Dually, $`N_{\max}(N_{\max}(v)) = v` for every target $`v`, and $`|T| \le |S|`.
Both maps are then bijections between $`S` and $`T`, which gives the two
perfect matchings.
:::

:::lemma_ "lem:bal-dismountability" (uses := "def:extremally-matched, def:between, def:spanner-from-to, thm:source-dismountability, lem:extremally-matched-of-not-dismountable, lem:extremally-matched-basic") (lean := "TemporalGraph.Subgraph.exists_isExtremallyMatched_reduction")
*Dismountability — Baligács Lemma 5.* Let $`G` be symmetric and $`H` a finite, simple,
symmetric bi-clique subgraph on $`S` and $`T`.
There are $`S' \subseteq S` and $`T' \subseteq T` such that the bi-clique
$`H[S' \cup T']` induced on them is extremally matched on $`S'` and $`T'`, and
every symmetric one-sided spanner $`K` of $`H[S' \cup T']` from $`S'` to $`T'`
extends to a symmetric one-sided spanner $`K'` of $`H` from $`S` to $`T` with
$$`
  |K'| + 2(|S'| + |T'|) \le |K| + 2(|S| + |T|),
`
that is, with at most $`2(|S| + |T| - |S'| - |T'|)` more edges. The bound is
additive, which avoids truncated subtraction, and no properness is needed.
:::

:::proof "lem:bal-dismountability"
By strong induction on $`|S| + |T|`. If a part is empty, take
$`S' = T' = \emptyset` and $`K' = K`. If some vertex $`x` is dismountable,
recurse on the bi-clique without $`x` and add the two edges of
{bpref "thm:source-dismountability"}[], two edges for one vertex less.
Otherwise $`H` itself is extremally matched
({bpref "lem:extremally-matched-of-not-dismountable"}[]): take $`S' = S`,
$`T' = T` and $`K' = K`.
:::

# Cuts in stars (Baligács §3)

:::definition "def:simple-star-cut-crossing" (uses := "def:extremally-matched, def:arc-time, def:neighbor-functions, def:temporal-walk, def:incidence-set") (lean := "TemporalGraph.eMin, TemporalGraph.eMax, TemporalGraph.incidentEdges, TemporalGraph.simpleStar, TemporalGraph.IsCutCrossing")
*Simple star and cut-crossing sources — Baligács Definition 8.* Let $`G` be an extremally
matched bi-clique and $`s^* \in S`. The matchings
$`E_{\min}` and $`E_{\max}` are the sets `eMin`$`(S)` and
`eMax`$`(S)` of the edges $`\{v, N_{\min}(v)\}` and $`\{v, N_{\max}(v)\}`
for $`v \in S`, at their times.

* (i) The _simple star_ $`\mathrm{Star}(s^*)` consists of $`E_{\min}`
  and of the edges at $`s^*` (`incidentEdges`).
* (ii) In the $`s^*`-ordered labeling, where the targets
  $`t_0, \ldots, t_{n-1}` are sorted by the times of their edges to $`s^*` and
  $`s_i = N_{\min}(t_i)`, the index of a target $`u` is read on
  $`\mathrm{arcTime}(s^*, u)` and that of a source $`v` on
  $`\mathrm{arcTime}(s^*, N_{\min}(v))`. For a cut given by a threshold
  $`\tau`, a source $`v` is _$`m`-hop-cut-crossing_ if its index is above
  the cut ($`\tau` is less than the time of $`s^*N_{\min}(v)`) and some
  temporal walk of length at most $`m` goes from $`v` to a target
  $`t_j = N_{\min}(s_j)` whose edge to $`s^*` has time at most $`\tau`, ending
  no later than the edge $`\{t_j, s^*\}`.
:::

:::lemma_ "lem:reachable-simple-star" (uses := "def:simple-star-cut-crossing, lem:walk-edges") (lean := "TemporalGraph.IsExtremallyMatched.exists_reachable_simpleStar")
*Simple stars cover the cut — Baligács Observation 9.* Let $`H` be a finite, simple, proper,
symmetric extremally matched bi-clique subgraph, $`s^* \in S`,
$`\tau` a threshold and $`m` a length, and let $`S_{\mathrm{cross}}` be the
$`m`-hop-cut-crossing sources. There is a set $`E` of at most
$`m\,|S_{\mathrm{cross}}|` edges of $`H` such that, in
$`\mathrm{fromEdgeSet}(E \cup \mathrm{Star}(s^*))`, every source that is
early (the time of $`s^*N_{\min}(v)` is at most $`\tau`) or crossing reaches
every target $`u` such that some value of $`\mathrm{arcTime}(s^*, u)` is at least
$`\tau`.
:::

:::proof "lem:reachable-simple-star"
An early source $`s_j` reaches an upper target $`t` through
$`s_j \to t_j \to s^* \to t`: the edge $`s_j t_j` is the earliest at $`t_j`, and
the times at $`s^*` increase along the labeling. A crossing source follows its
own walk, whose at most $`m` edges form $`E`
({bpref "lem:walk-edges"}[]), to some lower $`t_j`, then continues through
$`t_j \to s^* \to t` using only edges of $`\mathrm{Star}(s^*)`.
:::

# Extended stars (Baligács §4)

:::definition "def:extended-star" (uses := "def:simple-star-cut-crossing") (lean := "TemporalGraph.IsSourceExtendTarget, TemporalGraph.IsTargetExtendSource, TemporalGraph.extStarSource, TemporalGraph.extStarTarget")
*Extended stars — Baligács Definition 12.* Let $`s^* \in S` and $`t^* \in T`.

* (a) The _extend target_ of a vertex $`v` is the last target $`u`,
  in the $`s^*`-ordered labeling, whose edge to $`v` comes after its edge to
  $`s^*` (`IsSourceExtendTarget`). The _extended star_
  $`\mathrm{Ext}(s^*)` (`extStarSource`) consists of $`E_{\min}`,
  $`E_{\max}`, all the edges at $`s^*`, and the edge from each source to its
  extend target.
* (b) The _extend source_ of a vertex $`v` is the last source $`u`, in
  the $`t^*`-ordered labeling (sources by decreasing time at $`t^*`, and
  $`t_i = N_{\max}(s_i)`), whose edge to $`v` comes before its edge to $`t^*`
  (`IsTargetExtendSource`). The extended star $`\mathrm{Ext}(t^*)`
  (`extStarTarget`) consists of $`E_{\min}`, $`E_{\max}`, all the edges at
  $`t^*`, and the edge from each target to its extend source.

“Last” is read on arc times at the center: $`u'` is no later than $`u` when
some value of $`\mathrm{arcTime}(s^*, u')` is at most some value of
$`\mathrm{arcTime}(s^*, u)`; at the center $`t^*`, ordered by decreasing time, the
comparison is reversed.
:::

:::lemma_ "lem:ext-star-reachable" (uses := "def:extended-star, lem:extremally-matched-basic") (lean := "TemporalGraph.IsExtremallyMatched.reachable_extStarSource, TemporalGraph.IsExtremallyMatched.reachable_extStarTarget")
*Pairs reached by extended stars — Baligács Lemma 13.*

* (a) In the $`s^*`-ordered labeling, let $`u'` be a target,
  $`z = N_{\max}(u')` and $`u` the extend target of $`z`. For a source $`v` with
  $`x = N_{\min}(v)` whose edge to $`s^*` is no later than $`u s^*`, the star
  $`\mathrm{Ext}(s^*)` reaches $`u'` from $`v`.
* (b) Dually, in the $`t^*`-ordered labeling, for a source $`v` and
  $`\mathrm{Ext}(t^*)` reaching the targets whose $`N_{\max}` lies no later
  than the extend source of $`N_{\min}(v)`.
:::

:::proof "lem:ext-star-reachable"
For (a), the walk $`(v, x, s^*, u, z, u')` lies in $`\mathrm{Ext}(s^*)` and is
temporal: $`vx` is the earliest edge at $`x`, the times at $`s^*` increase with
the index, the definition of the extend target orders the edges at $`u`, and
$`zu'` is the latest edge at $`z`. Part (b) uses the dual walk through $`t^*`.
:::

:::lemma_ "lem:ext-star-not-reachable" (uses := "lem:ext-star-reachable") (lean := "TemporalGraph.IsExtremallyMatched.arcTime_le_of_not_reachable_extStarSource, TemporalGraph.IsExtremallyMatched.arcTime_le_of_not_reachable_extStarTarget")
*Pairs not reached by extended stars — Baligács Lemma 14.* Let $`v \in S`, $`u' \in T`,
$`x = N_{\min}(v)` and $`z = N_{\max}(u')`.

* (a) If $`\mathrm{Ext}(s^*)` does not reach $`u'` from $`v`, then
  $`\{x, z\}` occurs no later than $`\{x, s^*\}`.
* (b) If $`\mathrm{Ext}(t^*)` does not reach $`u'` from $`v`, then
  $`\{z, t^*\}` occurs no later than $`\{z, x\}`.
:::

:::proof "lem:ext-star-not-reachable"
For (a), suppose the converse inequality. Then the set of targets $`y` whose
edge to $`s^*` is before its edge to $`z` is nonempty, as it contains $`x`, so
$`z` has an extend target, and that one comes no earlier than $`x` in the
labeling. {bpref "lem:ext-star-reachable"}[] (a) then gives a walk from $`v`
to $`u'`, a contradiction. Part (b) is dual.
:::

:::corollary "cor:ext-star-chain" (uses := "lem:ext-star-not-reachable") (lean := "TemporalGraph.IsExtremallyMatched.arcTime_chain_of_not_reachable")
*Ordering of unreached pairs — Baligács Corollary 15.* If
$`\mathrm{Ext}(s^*) \cup \mathrm{Ext}(t^*)` does not reach $`u'` from $`v`,
then the walk $`(N_{\min}(t^*), t^*, N_{\max}(u'), N_{\min}(v), s^*)` is
temporal. Its first junction is temporal for free, $`N_{\min}(t^*)` being the
earliest neighbor of $`t^*`; the statement gives the other two inequalities,
at $`N_{\max}(u')` and at $`N_{\min}(v)`.
:::

:::proof "cor:ext-star-chain"
Neither extended star reaches $`u'` from $`v`: apply both parts of
{bpref "lem:ext-star-not-reachable"}[], and use the symmetry of arc times
to align the two inequalities.
:::

:::lemma_ "lem:cut-crossing-or-reachable" (uses := "cor:ext-star-chain, def:simple-star-cut-crossing, def:extended-star") (lean := "TemporalGraph.IsExtremallyMatched.isCutCrossing_or_reachable")
*Crossing or reaching — Baligács Lemma 16.* In the $`s^*`-ordered labeling cut at a threshold
$`\tau`, every source $`v`
above the cut either is $`3`-hop-cut-crossing, or
$`\mathrm{Ext}(s^*) \cup \mathrm{Ext}(N_{\min}(v))` reaches every target from
every source $`s_j` below the cut.
:::

:::proof "lem:cut-crossing-or-reachable"
Suppose some pair $`(s_j, u')` with $`s_j` below the cut is not reached. By
{bpref "cor:ext-star-chain"}[] with $`t^* = N_{\min}(v)`, whose earliest
neighbor is $`v`, the walk $`(v, N_{\min}(v), N_{\max}(u'), t_j, s^*)` is
temporal. Its first three edges reach the lower target $`t_j` no later than
the edge $`\{t_j, s^*\}`, so $`v` is $`3`-hop-cut-crossing.
:::

:::lemma_ "lem:ext-star-ncard" (uses := "def:extended-star") (lean := "TemporalGraph.IsExtremallyMatched.ncard_extStar_union_le")
*Size of two extended stars — Baligács, proof of Lemma 17.*
$`|\mathrm{Ext}(s^*) \cup \mathrm{Ext}(t^*)| \le 6n`, where $`n = |S|`.
:::

:::proof "lem:ext-star-ncard"
The union consists of six groups of at most $`n` edges each: $`E_{\min}`,
$`E_{\max}`, the edges at $`s^*`, the edges at $`t^*`, at most one extend edge
per source and at most one per target (extend targets and sources are
unique, by properness).
:::

:::lemma_ "lem:exists-threshold" (lean := "Set.exists_median_threshold")
*Median threshold.* For a finite set $`A` and any $`f : V \to \mathbb{N}`, some threshold
$`\tau`
leaves at most $`\lfloor |A| / 2 \rfloor` elements of $`A` with $`f < \tau` and
at most $`\lfloor |A| / 2 \rfloor` with $`f > \tau`.
:::

:::proof "lem:exists-threshold"
Take for $`\tau` the least value leaving more than $`\lfloor |A| / 2 \rfloor`
elements with $`f \le \tau`; it exists since $`f` is bounded on $`A`. By
minimality, fewer elements have $`f < \tau`, and the elements with $`f > \tau`
form the complement of a set of more than $`\lfloor |A| / 2 \rfloor` elements.
:::

:::lemma_ "lem:reachable-half" (uses := "lem:reachable-simple-star, lem:cut-crossing-or-reachable, lem:ext-star-ncard") (lean := "TemporalGraph.IsExtremallyMatched.exists_reachable_of_threshold")
*Reaching half of the bi-clique — Baligács Lemma 17.* Let $`H` be a finite, simple, proper,
symmetric extremally matched bi-clique
subgraph, $`s^* \in S`, and $`\tau` an arbitrary threshold time cutting the
$`s^*`-ordered labeling. Some set $`E` of at most $`6|S|` edges of $`H`,
containing $`E_{\min} \cup E_{\max}`, is such that in
$`\mathrm{fromEdgeSet}(E)` either every source reaches every target above the
cut (some value of $`\mathrm{arcTime}(s^*, u)` is at least $`\tau`), or every
source below the cut (the time of $`s^*N_{\min}(v)` is at most $`\tau`) reaches
every target.
:::

:::proof "lem:reachable-half"
If every source above the cut is $`3`-hop-cut-crossing, Observation 9
({bpref "lem:reachable-simple-star"}[]) gives $`E'` with $`|E'| \le 3|S|` such
that $`E' \cup \mathrm{Star}(s^*) \cup E_{\max}`, of size at most
$`3|S| + 2|S| + |S|`, reaches every target above the cut from every source.
Otherwise some source $`v` above the cut is not crossing, and
$`\mathrm{Ext}(s^*) \cup \mathrm{Ext}(N_{\min}(v))`, of size at most $`6|S|`
({bpref "lem:ext-star-ncard"}[]), reaches every target from every source
below the cut by {bpref "lem:cut-crossing-or-reachable"}[].
:::

# Linear spanners of bi-cliques

:::theorem "thm:spanner-extremally-matched" (uses := "lem:reachable-half, lem:exists-threshold, lem:bal-dismountability, lem:extremally-matched-basic, thm:extremally-matched-tc, lem:spanner-from-to-split") (lean := "TemporalGraph.IsExtremallyMatched.exists_isSpannerFromTo_temporallyConnected")
*Extremally matched bi-cliques — Baligács Theorem 18 (and Theorem 6).* Let $`H` be a finite,
simple, proper, symmetric extremally matched bi-clique
subgraph on $`S` and $`T`, with $`n = |S| = |T|`. There is a symmetric
one-sided spanner of $`H` from $`S` to $`T` with at most $`14n` edges, which is
moreover temporally connected on $`S \cup T`.
:::

:::proof "thm:spanner-extremally-matched"
By strong induction on $`n`, with a spanner containing
$`E_{\min} \cup E_{\max}`. Cut the $`s^*`-ordered labeling at a median threshold
({bpref "lem:exists-threshold"}[]) and apply
{bpref "lem:reachable-half"}[]: at most $`6n` edges reach every target above
the cut from every source, or every target from every source below the cut.
What is left, a bi-clique with one side of size at most $`\lfloor n/2 \rfloor`,
is reduced by {bpref "lem:bal-dismountability"}[] to an extremally matched
bi-clique of size $`x \le \lfloor n/2 \rfloor`; the induction hypothesis
spans it with $`14x` edges, which {bpref "lem:bal-dismountability"}[] extends
to the whole leftover with at most $`10 \lfloor n/2 \rfloor + 2(n + \lfloor n/2 \rfloor)`
edges, for a total of at most $`14n` (the two halves are glued by
{bpref "lem:spanner-from-to-split"}[]). Since the spanner contains $`E_{\min}`
and $`E_{\max}`, {bpref "thm:extremally-matched-tc"}[] gives temporal
connectivity on $`S \cup T`.
:::

:::theorem "thm:linear-biclique-spanner" (uses := "lem:bal-dismountability, thm:spanner-extremally-matched, def:spanner-from-to") (lean := "TemporalGraph.Subgraph.exists_isSpannerFromTo_ncard_le_linear")
*Linear spanners of temporal bi-cliques — Baligács Theorem 3.* Let $`G` be symmetric and
loopless and $`H` a finite, simple, proper,
symmetric temporal bi-clique subgraph on $`S` and $`T`. Then $`H` has a
symmetric one-sided spanner from $`S` to $`T`
({bpref "def:spanner-from-to"}[]) with at most
$`10 \min(|S|, |T|) + 2(|S| + |T|)` edges, to be compared with the
$`O(n \log n)` bound of {bpref "thm:exists-spanner-from-to-ncard-le"}[].
:::

:::proof "thm:linear-biclique-spanner" (uses := "thm:exists-spanner-from-to-ncard-le")
{bpref "lem:bal-dismountability"}[] gives $`S'`, $`T'` with
$`x = |S'| = |T'| \le \min(|S|, |T|)` ({bpref "lem:extremally-matched-basic"}[])
and an extremally matched bi-clique, which {bpref "thm:spanner-extremally-matched"}[]
spans with at most $`14x` edges. The extension of {bpref "lem:bal-dismountability"}[]
has $`|K'| + 2(|S'| + |T'|) \le 14x + 2(|S| + |T|)`, that is
$`|K'| \le 10x + 2(|S| + |T|)`.
:::

# Linear spanners of temporal cliques (Baligács §5)

:::theorem "thm:extremally-matched-of-not-two-hop" (uses := "def:extremally-matched, def:two-hop-dismountable, def:vminus-vplus-vzero, def:between, cor:biclique-of-not-two-hop, lem:reciprocity, lem:vminus-vplus-matchings, lem:earliestEdge-exists-finite-clique") (lean := "TemporalGraph.Subgraph.isExtremallyMatched_between_of_not_twoHopDismountable")
*Non-dismountable cliques give extremally matched bi-cliques — Baligács Theorem 20.* Let $`H` be
a finite, nontrivial, simple, proper, symmetric clique that is not
$`\{1,2\}`-hop dismountable. Then the restriction
$`H.\mathrm{between}(V^-, V^+)` of $`H` to the edges between $`V^-` and $`V^+` is
an extremally matched bi-clique with sources $`V^+` and targets $`V^-`. This is
the paper's Theorem 20, quoted there from SAND 2025, Corollary 4.1.
:::

:::proof "thm:extremally-matched-of-not-two-hop"
The restriction is a bi-clique by {bpref "cor:biclique-of-not-two-hop"}[].
The earliest edge $`va` of $`H` at $`v \in V^+` goes to $`a \in V^-`
({bpref "lem:vminus-vplus-matchings"}[]), and by reciprocity
({bpref "lem:reciprocity"}[], SAND 2025, Lemma 3.5) the edges from $`a` to
$`V^+` occur no earlier: it is the earliest edge at both ends in the
bi-clique. Every vertex of $`V^-` ends such an edge, which gives $`E_{\min}`;
$`E_{\max}` is dual.
:::

:::theorem "thm:spanner-of-not-two-hop-linear" (uses := "thm:extremally-matched-of-not-two-hop, thm:spanner-extremally-matched, lem:vzero-empty, lem:card-bounds, def:spanner") (lean := "TemporalGraph.Subgraph.exists_isSpannerOf_ncard_le_seven_mul_of_not_twoHopDismountable")
*Spanner of a non-dismountable clique, linear size — Baligács, proof of Theorem 2.* Let $`G` be
symmetric and loopless. A finite, nontrivial, simple, proper,
symmetric clique $`H` that is not $`\{1,2\}`-hop dismountable has a symmetric
spanner with at most $`14|V^+| = 7|\mathrm{Verts}(H)|` edges.
:::

:::proof "thm:spanner-of-not-two-hop-linear"
{bpref "thm:spanner-extremally-matched"}[] applied to the extremally matched
bi-clique of {bpref "thm:extremally-matched-of-not-two-hop"}[] gives a
one-sided spanner with at most $`14|V^+|` edges, temporally connected on
$`V^+ \cup V^-`. Since $`V^0 = \emptyset` ({bpref "lem:vzero-empty"}[]), this
is all of $`\mathrm{Verts}(H)`, so it is a spanner of the clique $`H`, and
$`|V^-| = |V^+|` ({bpref "lem:card-bounds"}[]) gives
$`|\mathrm{Verts}(H)| = 2|V^+|`.
:::

:::theorem "thm:clique-spanner-seven-mul" (uses := "thm:clique-induction, thm:spanner-of-not-two-hop-linear") (lean := "TemporalGraph.Subgraph.exists_isSpannerOf_ncard_le_seven_mul")
*Temporal cliques admit spanners of size $`7n` — Baligács Theorem 2.* Let $`G` be symmetric and
loopless. Every finite, simple, proper, symmetric
clique $`H` on $`n` vertices has a symmetric spanner with at most $`7n` edges.
:::

:::proof "thm:clique-spanner-seven-mul"
An instance of the generic clique induction {bpref "thm:clique-induction"}[] (the paper's
Observation 19, which is SAND 2025, Theorem 2.1 and §2.1), reused unchanged from the
$`O(n \log n)` bound, with $`f(n) = 7n`. Only two obligations are new: the step
$`7n + 4 \le 7(n + 1)`, and the non-dismountable case,
{bpref "thm:spanner-of-not-two-hop-linear"}[].
:::

:::theorem "thm:linear-main" (uses := "thm:clique-spanner-seven-mul") (lean := "TemporalGraph.Subgraph.exists_isBigO_isSpannerOf_linear")
*Linear spanners of temporal cliques — Baligács Theorem 2, answering Question 1.* There is a
function $`f(n) = O(n)`, chosen once for all temporal cliques, such
that every finite, simple, proper temporal clique $`H` on $`n` vertices (with
$`H` and its ambient graph symmetric, the ambient graph loopless) admits a
symmetric spanner with at most $`f(n)` edges. One can take $`f(n) = 7n`. This
improves {bpref "thm:main-spanner-bound"}[].
:::

:::proof "thm:linear-main"
Take $`f(n) = 7n`, which bounds the spanners of every such clique by
{bpref "thm:clique-spanner-seven-mul"}[], and is trivially $`O(n)`.
:::
