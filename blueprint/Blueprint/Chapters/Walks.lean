import Verso
import VersoManual
import VersoBlueprint
import Blueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Walks and reachability" =>

%%%
tag := "chap:walks"
%%%

A _temporal walk_ is a sequence of edges whose times are non-decreasing (a _non-strict_ walk:
several edges may be crossed at the same time); a _non-empty_ temporal walk additionally requires
at least one edge. A walk is _strict_ when its times increase strictly. Walks are formalized in
`TemporalGraph/TemporalWalk.lean` and `TemporalGraph/NonemptyTemporalWalk.lean` (which also define
strictness). Reachability, strict reachability and temporal connectivity live in
`TemporalGraph/Connectivity/Basic.lean`.

:::definition "def:temporal-walk" (uses := "def:temporal-graph") (lean := "TemporalGraph.TemporalWalk, TemporalGraph.NonemptyTemporalWalk")
*Temporal walk.* A _temporal walk_ from $`x` at time $`n` to $`y` at time $`m` is either the
empty walk (when $`x = y`, $`n = m`) or a non-empty temporal walk: a sequence of edges
$`(x_0,x_1,t_1), (x_1,x_2,t_2), \dots` with $`x_0 = x`, times non-decreasing, ending at $`y` at
time $`m`.
:::

:::definition "def:walk-invariants" (uses := "def:temporal-walk") (lean := "TemporalGraph.TemporalWalk.length, TemporalGraph.TemporalWalk.support, TemporalGraph.TemporalWalk.arcs, TemporalGraph.NonemptyTemporalWalk.length, TemporalGraph.NonemptyTemporalWalk.support, TemporalGraph.NonemptyTemporalWalk.arcs")
*Length, support, arcs of a walk.* The _length_ of a temporal walk is its number of edges; its
_support_ is the list of vertices it visits (stored from the end vertex back to the start); its
_arcs_ is the list of directed edges $`(x_i, x_{i+1}, t_{i+1})` it traverses (stored last arc
first).
:::

:::lemma_ "lem:nondecreasing-time" (uses := "def:temporal-walk") (lean := "TemporalGraph.TemporalWalk.nondecreasing_time, TemporalGraph.NonemptyTemporalWalk.nondecreasing_time")
*Non-decreasing time.* A temporal walk from $`x` at time $`n` to $`y` at time $`m` satisfies
$`n \le m`.
:::

:::proof "lem:nondecreasing-time"
Induction on the walk: a one-edge walk starts and ends at the same time, and each further edge has
a time at least that of the previous end.
:::

:::definition "def:reachable" (uses := "def:temporal-walk") (lean := "TemporalGraph.Reachable, TemporalGraph.TemporallyConnected, TemporalGraph.TemporallyConnectedGraph, TemporalGraph.Subgraph.TemporallyConnectedSubgraph, TemporalGraph.Reachable.mono")
*Reachability, temporal connectivity.* $`y` is _reachable_ from $`x` in $`G` if there is a
temporal walk from $`x` to $`y` (at some times $`n \le m`); the walk may be empty, so every vertex
reaches itself. A set $`S` of vertices is _temporally connected_ in $`G` (denoted
$`G.\mathrm{TemporallyConnected}\,S`) if every vertex of $`S` reaches every vertex of $`S`. $`G`
_is temporally connected_ (shorthand $`G.\mathrm{TemporallyConnectedGraph}`) if all of $`V` is
temporally connected; a sub-temporal-graph $`H` is temporally connected (shorthand
$`H.\mathrm{TemporallyConnectedSubgraph}`) if all of $`\mathrm{Verts}(H)` is. Reachability is
_monotone_: if $`H \le H'`, then
$`H.\mathrm{Reachable}\,x\,y \Rightarrow H'.\mathrm{Reachable}\,x\,y`.
:::

:::definition "def:strict-reachable" (uses := "def:temporal-walk, def:reachable") (lean := "TemporalGraph.NonemptyTemporalWalk.IsStrict, TemporalGraph.TemporalWalk.IsStrict, TemporalGraph.StrictReachable, TemporalGraph.StrictReachable.mono")
*Strict walk, strict reachability.* A temporal walk is _strict_ if its times increase strictly
from each arc to the next; the empty walk is strict. $`y` is _strictly reachable_ from $`x` if
some strict temporal walk goes from $`x` to $`y`. Strict reachability implies reachability and is
monotone along $`\le`.
:::

:::lemma_ "lem:reachable-iff-strict" (uses := "def:strict-reachable, def:is-symm-loopless, def:is-proper-happy") (lean := "TemporalGraph.NonemptyTemporalWalk.exists_isStrict, TemporalGraph.reachable_iff_strictReachable")
*Strict and non-strict reachability agree in proper symmetric graphs.* If $`G` is symmetric and
proper, then $`y` is reachable from $`x` if and only if it is strictly reachable from $`x`.
:::

:::proof "lem:reachable-iff-strict"
Walks themselves differ: crossing an edge and immediately crossing it back at the same time is a
non-strict walk that is not strict. Consider two consecutive arcs $`w \to y \to z` of a walk with
the same time $`t`. By symmetry, $`y` has the two edges $`yw` and $`yz` at time $`t`, so
properness forces $`w = z`: the two arcs are a round trip, which can be deleted. The arc before
them arrives at $`w` no later than $`t`, and the arc after them leaves $`z = w` no earlier than
$`t`, so the shortened walk is still a temporal walk. Repeating this yields a strict walk,
possibly empty. Symmetry is needed: in the oriented, proper graph with the two arcs $`a \to y` and
$`y \to z` at time $`1`, $`a` reaches $`z` but not strictly.
:::

:::lemma_ "lem:clique-temporally-connected" (uses := "def:reachable, def:is-simple-clique") (lean := "TemporalGraph.temporallyConnected_of_isClique")
*Cliques are temporally connected.* If $`S` forms a clique in $`G`
({bpref "def:is-simple-clique"}[]), then $`S` is temporally connected in $`G`.
:::

:::proof "lem:clique-temporally-connected" (uses := "def:reachable")
Two distinct vertices of $`S` are joined by an arc, which is a one-edge walk; a vertex reaches
itself by the empty walk.
:::

:::lemma_ "lem:reachable-of-earliestEdge" (uses := "def:reachable, def:earliest-latest-neighbor") (lean := "TemporalGraph.reachable_of_earliestEdge, TemporalGraph.reachable_of_extended_earliestEdge")
*Reachability through an earliest edge.* Assume $`G` is symmetric. If $`(x,y,n)` is the earliest
edge of $`x` ({bpref "def:earliest-latest-neighbor"}[]), every vertex reachable from $`x` is also
reachable from $`y`: prepend the edge $`y \to x` at time $`n` (using symmetry) to a walk out of
$`x`, which stays non-decreasing since $`n` is a lower bound on all of $`x`'s times. More
generally, if some vertex $`z` has an edge to $`y` at a time $`m \le n`, then $`z` too reaches
everything $`x` reaches, via $`z \to y \to x \to \cdots`.
:::

:::proof "lem:reachable-of-earliestEdge" (uses := "lem:nondecreasing-time")
Take a walk from $`x` to $`z`. If it is empty, the reversed edge $`y \to x` at time $`n` (by
symmetry) is a walk to $`x = z`. Otherwise prepend this edge to the walk: it is admissible because
$`n` is at most the time of every edge at $`x`, in particular of the first edge of the walk. For
the extended version, prepend $`z \to y` at time $`m \le n` followed by $`y \to x` at time $`n`.
:::

:::lemma_ "lem:reachable-of-latestEdge" (uses := "def:reachable, def:earliest-latest-neighbor") (lean := "TemporalGraph.reachable_of_latestEdge, TemporalGraph.reachable_of_extended_latestEdge")
*Reachability through a latest edge.* Dually: assume $`G` is symmetric. If $`(x,y,n)` is the
latest edge of $`x`, every vertex that reaches $`x` also reaches $`y`: append the edge
$`x \to y` at time $`n`, an upper bound on all of $`x`'s times. More generally, if $`y` has an
edge to some vertex $`z` at a time $`m \ge n`, then everything that reaches $`x` also reaches
$`z`, via $`\cdots \to x \to y \to z`.
:::

:::proof "lem:reachable-of-latestEdge" (uses := "lem:nondecreasing-time")
Take a walk from $`z` to $`x`. If it is empty, the edge $`x \to y` at time $`n` is a walk.
Otherwise append this edge to the walk: it is admissible because $`n` is at least the time of
every edge at $`x`, in particular of the last edge of the walk. For the extended version, append
$`x \to y` at time $`n` followed by $`y \to z` at time $`m \ge n`.
:::
