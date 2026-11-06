import Verso
import VersoManual
import VersoBlueprint
import Blueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Main results" =>

%%%
tag := "chap:main-theorem"
%%%

Casteigts, Peters and Schoeters (_Temporal Cliques Admit Sparse Spanners_, ICALP 2019 / JCSS 2021)
showed that every temporal clique on $`n` vertices admits a spanner with $`O(n \log n)` edges, and
asked whether $`O(n)` is possible. The library formalizes two answers, both complete:

* the $`O(n \log n)` bound, through the dismountability-only proof of Daniele Carnevale, Arnaud
  Casteigts and Timothée Corsini, _Dismountability in Temporal Cliques Revisited_, SAND 2025
  (LIPIcs 330, 6:1–6:18, doi:10.4230/LIPIcs.SAND.2025.6, arXiv:2502.01321), §§2–4, which
  concludes with the one-sided dismountability of Angrick et al. (ESA 2024):
  {bpref "thm:main-spanner-bound"}[] below, with the explicit bound
  $`2n\lceil\log_2 n\rceil + 4n` ({bpref "thm:clique-spanner-ncard-le"}[]);
* the linear bound, at most $`7n` edges, which answers the question: Júlia Baligács, _Temporal
  Cliques Admit Linear Spanners_, arXiv:2606.05156v1 (2026), formalized in
  {ref "chap:linear-spanners"}[Linear spanners]
  ({bpref "thm:clique-spanner-seven-mul"}[] and {bpref "thm:linear-main"}[]).

Both are stated for finite, simple, proper temporal cliques. The reductions of the papers to the
simple and proper case are not formalized: these properties are hypotheses.

:::theorem "thm:main-spanner-bound" (uses := "thm:clique-spanner-ncard-le, thm:spanner-bound-isBigO") (lean := "TemporalGraph.Subgraph.exists_isBigO_isSpannerOf")
*$`O(n \log n)` spanners of temporal cliques — SAND §4.1.* There is a function
$`f(n) = O(n \log n)`, chosen once for all temporal cliques, such that every finite, simple, proper
temporal clique $`H` on $`n` vertices (with $`H` and its ambient graph symmetric, the ambient graph
loopless) admits a symmetric spanner $`K` of $`H` ({bpref "def:spanner"}[]) with at most $`f(n)`
edges. One can take $`f(n) = 2n\lceil\log_2 n\rceil + 4n` ({bpref "thm:clique-spanner-ncard-le"}[]).
:::

:::proof "thm:main-spanner-bound"
Take $`f(n) = 2n\lceil\log_2 n\rceil + 4n`, which bounds the spanners of every such clique by
{bpref "thm:clique-spanner-ncard-le"}[]. Since $`\lceil\log_2 n\rceil \le \log_2 n + 1` and
$`1 \le \log_2 n` for $`n \ge 2`, $`f(n) \le 8 n \log_2 n` eventually, so $`f(n) = O(n \log n)`.
:::

# One proof engine, two bounds

Both bounds are proved by the same generic induction on the number $`n` of vertices,
{bpref "thm:clique-induction"}[]. Its statement takes the bound $`f` as a parameter, and each
result only supplies what is specific to it.

*Shared: the dismountable case.* If $`H` is $`\{1,2\}`-hop dismountable
({bpref "def:two-hop-dismountable"}[]), some vertex $`x` can be dismounted: a spanner of $`H - x`,
given by induction, extends to a spanner of $`H` with at most $`4` more edges
({bpref "thm:spanner-of-two-hop-dismountable"}[]). Each bound only checks
$`f(n) + 4 \le f(n + 1)`.

*Shared: the structure of a non-dismountable clique.* Then $`V^0 = \emptyset`
({bpref "lem:vzero-empty"}[]), $`|V^-| = |V^+|` ({bpref "thm:neighbor-fn-bijective"}[]), so
$`n = 2|V^+|`, and the edges between $`V^-` and $`V^+` form a temporal bi-clique
({bpref "cor:biclique-of-not-two-hop"}[]) whose earliest and latest edges are perfect matchings
({bpref "lem:vminus-vplus-matchings"}[], {bpref "lem:reciprocity"}[]).

*Specific to $`O(n \log n)`.* A one-sided spanner of the bi-clique from $`V^+` to $`V^-`, of size
$`\mathrm{spannerBound}(|V^+|)` ({bpref "thm:exists-spanner-from-to-ncard-le"}[]), together with
the two matchings, is a spanner of $`H` ({bpref "thm:spanner-of-not-two-hop-dismountable"}[]). The
one-sided bound comes from the halving recurrence of Angrick et al.:
$`\mathrm{spannerBound}(n) \le 2n\lceil\log_2 n\rceil + n`
({bpref "lem:spanner-bound-closed-form"}[]).

*Specific to $`7n`.* The bi-clique is extremally matched
({bpref "thm:extremally-matched-of-not-two-hop"}[]), and such bi-cliques have linear one-sided
spanners built from stars ({bpref "thm:spanner-extremally-matched"}[]), which gives the
non-dismountable case ({bpref "thm:spanner-of-not-two-hop-linear"}[]).
