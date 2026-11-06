import Verso
import VersoManual
import VersoBlueprint
import Blueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Main theorem: sparse spanners for temporal cliques" =>

%%%
tag := "chap:main-theorem"
%%%

This is the target result of the project, now fully formalized. It was first proved by Casteigts,
Peters and Schoeters, _Temporal Cliques Admit Sparse Spanners_, ICALP 2019 / JCSS. The formal proof
follows the dismountability-only proof of Daniele Carnevale, Arnaud Casteigts and Timothée Corsini,
_Dismountability in Temporal Cliques Revisited_, SAND 2025 (LIPIcs 330, 6:1–6:18,
doi:10.4230/LIPIcs.SAND.2025.6, arXiv:2502.01321), §§2–4, which concludes with the one-sided
dismountability of Angrick et al. (ESA 2024).

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

# Proof strategy

{bpref "thm:clique-spanner-ncard-le"}[] is proved by strong induction on the number $`n` of
vertices.

1. If $`H` is $`\{1,2\}`-hop dismountable ({bpref "def:two-hop-dismountable"}[]), some vertex
   $`x` can be dismounted: a spanner of $`H - x`, given by induction, extends to a spanner of $`H`
   with at most $`4` more edges ({bpref "thm:spanner-of-two-hop-dismountable"}[]).
2. Otherwise $`V^0 = \emptyset` ({bpref "lem:vzero-empty"}[]) and $`|V^-| = |V^+|`
   ({bpref "thm:neighbor-fn-bijective"}[]), so $`n = 2|V^+|`. The restriction of $`H` to the
   edges between $`V^-` and $`V^+` is a temporal bi-clique
   ({bpref "cor:biclique-of-not-two-hop"}[]). A one-sided spanner of this bi-clique from $`V^+`
   to $`V^-`, of size at most $`\mathrm{spannerBound}(|V^+|)`
   ({bpref "thm:exists-spanner-from-to-ncard-le"}[]), together with the two perfect matchings
   $`M^-` and $`M^+` ({bpref "lem:vminus-vplus-matchings"}[]), is a spanner of $`H`
   ({bpref "thm:spanner-of-not-two-hop-dismountable"}[]).
3. The one-sided bound comes from the halving recurrence of Angrick et al.:
   $`\mathrm{spannerBound}(n) \le 2n\lceil\log_2 n\rceil + n`
   ({bpref "lem:spanner-bound-closed-form"}[]).

The bound $`O(n \log n)` is not optimal: Baligács (arXiv:2606.05156v1) shows that temporal cliques
admit spanners of linear size, at most $`7n` edges. That result is formalized in
{ref "chap:linear-spanners"}[Linear spanners] ({bpref "thm:clique-spanner-seven-mul"}[] and
{bpref "thm:linear-main"}[]).
