/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.LinearSpanner.ExtremallyMatched

import TemporalGraph.Helpers.SetCard

/-!
# Stars of an extremally matched bi-clique

The edge sets and vertex predicates of Baligács 2026, §§3–4, on a temporal bi-clique with sources
`s` and targets `t`, with their membership and counting lemmas. The results about them are in
`LinearSpanner/SimpleStar.lean` (§3, Observation 9) and `LinearSpanner/ExtendedStar.lean` (§4,
Lemmas 13–16).

**Labelings without indices.** The paper numbers the vertices along the order induced by a center
(Definition 7). For a source center `c`, the targets are sorted by the times of their edges to
`c`, and the `i`-th source is the earliest neighbor `N_min` of the `i`-th target. We never build
these indices: "`j ≤ i`" is a comparison of arc times at the center. For a target `u` the index is
read on the times `k` with `G.Adj c u k`; for a source `v` on those of `G.Adj c w`, with
`w = N_min v`. A cut at `k`
(Definition 8) is a threshold time `τ`. For a target center the order is by decreasing time.

**Vocabulary used in this file and the next ones.** Write `λ(a, b)` for the time of the edge
`{a, b}`, that is the `k` with `G.Adj a b k`; `c` is the center and `τ` the threshold time of a
cut.

* `pos_x(z) ≤ pos_x(c)` : the edge `{x, z}` comes no later than the edge `{x, c}`, that is
  `∃ k, G.Adj x z k ∧ ∃ l, G.Adj x c l ∧ k ≤ l`. (`pos_x(z) < pos_x(c)` : the same with
  `k < l`.)
* *extend index* : see `IsSourceExtendTarget` and `IsTargetExtendSource`.
* an *early* source `v` (for the center `c` and the threshold `τ`) : `λ(c, N_min v) ≤ τ`, that is
  `∃ u ∈ G.earliestNeighborFn v, ∃ k, G.Adj c u k ∧ k ≤ τ` (the paper's `s_j`, `j ≤ k`). The
  set of early sources in `s` is `G.earlySources s c τ`.
* an *upper* source `v` : `τ < λ(c, N_min v)` (the paper's `s_i`, `i > k`). The set of upper
  sources in `s` is `G.upperSources s c τ`.
* a *late* target `u` : `τ ≤ λ(c, u)`. The set of late targets in `t` is `G.lateTargets t c τ`.
* a *crossing* source : an upper source from which a short temporal walk reaches an early source's
  `N_min`, before the edge of that `N_min` to `c` (see `IsCutCrossing`).

**Times through `Adj`, neighbors through `Option`.** A time comparison is stated on the adjacency
itself, `∃ k, G.Adj c u k ∧ k ≤ τ`, false when there is no arc, and exact in any graph (no
arbitrary choice among several times of an arc, unlike `arcTime`). The earliest and latest
neighbors are read on the `Option`-valued `earliestNeighborFn` and `latestNeighborFn`, through
their values (`∃ u ∈ G.earliestNeighborFn v, …`), never through the order of `Option`. In an
extremally matched bi-clique every arc and every such neighbor exists, and in a simple graph each
arc has one time, so nothing is lost.

## Main definitions

* `TemporalGraph.earlySources`, `TemporalGraph.upperSources`, `TemporalGraph.lateTargets` : the
  early sources, upper sources and late targets of a cut.
* `TemporalGraph.eMin`, `TemporalGraph.eMax` : the matchings `E_min` and `E_max`.
* `TemporalGraph.incidentEdges` : the edges from a vertex to a set.
* `TemporalGraph.simpleStar` : Definition 8 (i), the simple star `Star(c)`.
* `TemporalGraph.IsCutCrossing` : Definition 8 (ii), the `m`-hop-`k`-cut-crossing sources.
* `TemporalGraph.IsSourceExtendTarget`, `TemporalGraph.IsTargetExtendSource` : the extend index of
  Definition 12.
* `TemporalGraph.extStarSource`, `TemporalGraph.extStarTarget` : Definition 12, the extended stars
  `Ext(c)` from a source and from a target.

## Main results

* `TemporalGraph.simpleStar_subset_edgeSet`, `TemporalGraph.extStarSource_subset_edgeSet`,
  `TemporalGraph.extStarTarget_subset_edgeSet` : the stars consist of edges of the graph, with no
  hypothesis (their times are times of arcs).
* `TemporalGraph.ncard_eMin_le`, `TemporalGraph.ncard_eMax_le`,
  `TemporalGraph.ncard_incidentEdges_le` : in a simple graph, at most one edge per vertex of the
  indexing set.
* `TemporalGraph.IsExtremallyMatched.mem_eMin_of_mem_union`,
  `TemporalGraph.IsExtremallyMatched.mem_eMax_of_mem_union` :
  `E_min` and `E_max` also contain the earliest and latest edges at the targets.

## References

* Júlia Baligács, *Temporal Cliques Admit Linear Spanners*, arXiv:2606.05156v1 (2026), §§3–4.
-/

@[expose] public section

universe u

namespace TemporalGraph

variable {V : Type u} {G : TemporalGraph V} {s t A : Set V}

section Definitions

/-- The early sources of the cut at `τ`, for the center `c`: the sources `v ∈ s` whose
`N_min v` is joined to `c` at a time at most `τ` (Baligács 2026, §3: the sources `s_j` with
`j ≤ k`, the cut `k` being the threshold time `τ`). -/
abbrev earlySources (G : TemporalGraph V) (s : Set V) (c : V) (τ : ℕ) : Set V :=
  {v ∈ s | ∃ u ∈ G.earliestNeighborFn v, ∃ k, G.Adj c u k ∧ k ≤ τ}

/-- The upper sources of the cut at `τ`, for the center `c`: the sources `v ∈ s` whose `N_min v`
is joined to `c` at a time strictly after `τ` (Baligács 2026, §3: the sources `s_i` with `i > k`,
the cut `k` being the threshold time `τ`). -/
abbrev upperSources (G : TemporalGraph V) (s : Set V) (c : V) (τ : ℕ) : Set V :=
  {v ∈ s | ∃ u ∈ G.earliestNeighborFn v, ∃ k, G.Adj c u k ∧ τ < k}

/-- The late targets of the cut at `τ`, for the center `c`: the targets `u ∈ t` joined to `c` at
a time at least `τ` (Baligács 2026, §3: the targets `t_j` on the far side of the cut at `τ`). -/
abbrev lateTargets (G : TemporalGraph V) (t : Set V) (c : V) (τ : ℕ) : Set V :=
  {u ∈ t | ∃ k, G.Adj c u k ∧ τ ≤ k}

/-- The edges `{v, N_min(v)}` for `v ∈ A`, at their times. For an extremally matched bi-clique,
`G.eMin s` is the matching `E_min` of Baligács 2026, §2.3. -/
def eMin (G : TemporalGraph V) (A : Set V) : Set (Sym2 V × ℕ) :=
  {e | ∃ v ∈ A, ∃ w ∈ G.earliestNeighborFn v, ∃ n, G.Adj v w n ∧ e = (s(v, w), n)}

/-- The edges `{v, N_max(v)}` for `v ∈ A`, at their times. For an extremally matched bi-clique,
`G.eMax s` is the matching `E_max` of Baligács 2026, §2.3. -/
def eMax (G : TemporalGraph V) (A : Set V) : Set (Sym2 V × ℕ) :=
  {e | ∃ v ∈ A, ∃ w ∈ G.latestNeighborFn v, ∃ n, G.Adj v w n ∧ e = (s(v, w), n)}

/-- The edges from `x` to the vertices of `A`, at their times. -/
def incidentEdges (G : TemporalGraph V) (x : V) (A : Set V) : Set (Sym2 V × ℕ) :=
  {e | ∃ v ∈ A, ∃ n, G.Adj x v n ∧ e = (s(x, v), n)}

/-- Baligács 2026, Definition 8 (i): the simple star `Star(c)` from the source `c` consists of
`E_min` and of all the edges at `c`. -/
def simpleStar (G : TemporalGraph V) (s t : Set V) (c : V) : Set (Sym2 V × ℕ) :=
  G.eMin s ∪ G.incidentEdges c t

/-- Baligács 2026, Definition 8 (ii), with the cut `k` given by the threshold time `τ`: in the
`c`-ordered labeling, the source `v = sᵢ` is `m`-hop-`k`-cut-crossing when `i > k` (the first
conjunct: `τ < λ(c, N_min v)`, `v` is an upper source) and some temporal walk of length at most
`m + 1` starts at `v` and ends with the edge `{t_j, c}` for some `j ≤ k` (the second conjunct: `t_j`
is `N_min` of an early source). The walk is split into its part from `v` to `t_j = N_min(s_j)`, of
length at most `m`, and the final edge to `c`, which must come no earlier. -/
def IsCutCrossing (G : TemporalGraph V) (s : Set V) (c : V) (τ m : ℕ) (v : V) : Prop :=
  (∃ u ∈ G.earliestNeighborFn v, ∃ k, G.Adj c u k ∧ τ < k) ∧
    ∃ w ∈ s, ∃ u ∈ G.earliestNeighborFn w, (∃ k, G.Adj c u k ∧ k ≤ τ) ∧
      ∃ n n' : ℕ, ∃ p : G.TemporalWalk v n u n', p.length ≤ m ∧ ∃ k, G.Adj u c k ∧ n' ≤ k

/-- Baligács 2026, Definition 12 (a): for the source center `c` ("Source" refers to the side of the
center), `u` is the extend target of the source `v`, i.e. `u = t_{ind(v)}`: among the targets `u'`
with `λ(u', c) < λ(u', v)`, it is the one with the greatest `λ(c, u')`, that is, the last in the
`c`-ordered labeling. -/
def IsSourceExtendTarget (G : TemporalGraph V) (t : Set V) (c v u : V) : Prop :=
  u ∈ t ∧ (∃ a, G.Adj u c a ∧ ∃ b, G.Adj u v b ∧ a < b) ∧
    ∀ u' ∈ t, (∃ a, G.Adj u' c a ∧ ∃ b, G.Adj u' v b ∧ a < b) →
      ∃ a, G.Adj c u' a ∧ ∃ b, G.Adj c u b ∧ a ≤ b

/-- Baligács 2026, Definition 12 (b): for the target center `c` ("Target" refers to the side of the
center), `u` is the extend source of the target `v`, i.e. `u = s_{ind(v)}`: among the sources `u'`
with `λ(u', v) < λ(u', c)`, it is the one with the least `λ(c, u')`, that is, the last in the
`c`-ordered labeling (by decreasing time at `c`). -/
def IsTargetExtendSource (G : TemporalGraph V) (s : Set V) (c v u : V) : Prop :=
  u ∈ s ∧ (∃ a, G.Adj u v a ∧ ∃ b, G.Adj u c b ∧ a < b) ∧
    ∀ u' ∈ s, (∃ a, G.Adj u' v a ∧ ∃ b, G.Adj u' c b ∧ a < b) →
      ∃ a, G.Adj c u a ∧ ∃ b, G.Adj c u' b ∧ a ≤ b

/-- Baligács 2026, Definition 12 (a): the extend edges of `Ext(c)`, joining each source to the
target at its extend index (when it has one). -/
def sourceExtendEdges (G : TemporalGraph V) (s t : Set V) (c : V) : Set (Sym2 V × ℕ) :=
  {e | ∃ v ∈ s, ∃ u, G.IsSourceExtendTarget t c v u ∧ ∃ n, G.Adj v u n ∧ e = (s(v, u), n)}

/-- Baligács 2026, Definition 12 (b): the extend edges of `Ext(c)`, joining each target to the
source at its extend index (when it has one). -/
def targetExtendEdges (G : TemporalGraph V) (s t : Set V) (c : V) : Set (Sym2 V × ℕ) :=
  {e | ∃ v ∈ t, ∃ u, G.IsTargetExtendSource s c v u ∧ ∃ n, G.Adj u v n ∧ e = (s(u, v), n)}

/-- Baligács 2026, Definition 12 (a): the extended star `Ext(c)` from the source `c`: `E_min`,
`E_max`, all the edges at `c`, and the edge from each source to the target at its extend index. -/
def extStarSource (G : TemporalGraph V) (s t : Set V) (c : V) : Set (Sym2 V × ℕ) :=
  G.eMin s ∪ G.eMax s ∪ G.incidentEdges c t ∪ G.sourceExtendEdges s t c

/-- Baligács 2026, Definition 12 (b): the extended star `Ext(c)` from the target `c`: `E_min`,
`E_max`, all the edges at `c`, and the edge from each target to the source at its extend index. -/
def extStarTarget (G : TemporalGraph V) (s t : Set V) (c : V) : Set (Sym2 V × ℕ) :=
  G.eMin s ∪ G.eMax s ∪ G.incidentEdges c s ∪ G.targetExtendEdges s t c

end Definitions

section Membership

variable {v w x : V} {n : ℕ}

/-- The edge from `v ∈ A` to `N_min v` is in `G.eMin A`. -/
theorem mem_eMin (h₀ : v ∈ A) (h₁ : G.earliestNeighborFn v = some w)
    (h₂ : G.Adj v w n) : (s(v, w), n) ∈ G.eMin A :=
  ⟨v, h₀, w, h₁, n, h₂, rfl⟩

/-- The edge from `v ∈ A` to `N_max v` is in `G.eMax A`. -/
theorem mem_eMax (h₀ : v ∈ A) (h₁ : G.latestNeighborFn v = some w)
    (h₂ : G.Adj v w n) : (s(v, w), n) ∈ G.eMax A :=
  ⟨v, h₀, w, h₁, n, h₂, rfl⟩

/-- The edge from `x` to `v ∈ A` is in `G.incidentEdges x A`. -/
theorem mem_incidentEdges (h₀ : v ∈ A) (h₁ : G.Adj x v n) :
    (s(x, v), n) ∈ G.incidentEdges x A :=
  ⟨v, h₀, n, h₁, rfl⟩

end Membership

section Subset

/-- `G.eMin A` consists of edges of `G`. -/
theorem eMin_subset_edgeSet : G.eMin A ⊆ G.edgeSet := by
  rintro _ ⟨v, -, w, -, n, h₀, rfl⟩
  exact ⟨_, _, rfl, h₀⟩

/-- `G.eMax A` consists of edges of `G`. -/
theorem eMax_subset_edgeSet : G.eMax A ⊆ G.edgeSet := by
  rintro _ ⟨v, -, w, -, n, h₀, rfl⟩
  exact ⟨_, _, rfl, h₀⟩

/-- `G.incidentEdges x A` consists of edges of `G`. -/
theorem incidentEdges_subset_edgeSet {x : V} : G.incidentEdges x A ⊆ G.edgeSet := by
  rintro _ ⟨v, -, n, h₀, rfl⟩
  exact ⟨_, _, rfl, h₀⟩

/-- The extend edges of `Ext(c)`, `c` a source, are edges of `G`. -/
theorem sourceExtendEdges_subset_edgeSet {c : V} : G.sourceExtendEdges s t c ⊆ G.edgeSet := by
  rintro _ ⟨v, -, u, -, n, h₀, rfl⟩
  exact ⟨_, _, rfl, h₀⟩

/-- The extend edges of `Ext(c)`, `c` a target, are edges of `G`. -/
theorem targetExtendEdges_subset_edgeSet {c : V} : G.targetExtendEdges s t c ⊆ G.edgeSet := by
  rintro _ ⟨v, -, u, -, n, h₀, rfl⟩
  exact ⟨_, _, rfl, h₀⟩

/-- The simple star consists of edges of `G`. -/
theorem simpleStar_subset_edgeSet {c : V} : G.simpleStar s t c ⊆ G.edgeSet :=
  Set.union_subset eMin_subset_edgeSet incidentEdges_subset_edgeSet

/-- The extended star from a source consists of edges of `G`. -/
theorem extStarSource_subset_edgeSet {c : V} : G.extStarSource s t c ⊆ G.edgeSet := by
  simp only [extStarSource, Set.union_subset_iff]
  exact ⟨⟨⟨eMin_subset_edgeSet, eMax_subset_edgeSet⟩, incidentEdges_subset_edgeSet⟩,
    sourceExtendEdges_subset_edgeSet⟩

/-- The extended star from a target consists of edges of `G`. -/
theorem extStarTarget_subset_edgeSet {c : V} : G.extStarTarget s t c ⊆ G.edgeSet := by
  simp only [extStarTarget, Set.union_subset_iff]
  exact ⟨⟨⟨eMin_subset_edgeSet, eMax_subset_edgeSet⟩, incidentEdges_subset_edgeSet⟩,
    targetExtendEdges_subset_edgeSet⟩

end Subset

section Count

/-- In a simple graph, at most one edge of `E_min` per vertex of `A`: `N_min` is a function, and
each arc has one time. -/
theorem ncard_eMin_le (h₀ : G.IsSimple) (h₁ : A.Finite) : (G.eMin A).ncard ≤ A.ncard :=
  (Set.finite_and_ncard_le_of_functional (S := G.eMin A)
    (fun v e ↦ ∃ w ∈ G.earliestNeighborFn v, ∃ n, G.Adj v w n ∧ e = (s(v, w), n)) h₁
    (fun _ he ↦ he) fun _ _ _ ⟨w, hw, n, hn, he⟩ ⟨w', hw', n', hn', he'⟩ ↦ by
      obtain rfl := Option.mem_unique hw hw'
      obtain rfl := h₀ hn hn'
      rw [he, he']).2

/-- In a simple graph, at most one edge of `E_max` per vertex of `A`. -/
theorem ncard_eMax_le (h₀ : G.IsSimple) (h₁ : A.Finite) : (G.eMax A).ncard ≤ A.ncard :=
  (Set.finite_and_ncard_le_of_functional (S := G.eMax A)
    (fun v e ↦ ∃ w ∈ G.latestNeighborFn v, ∃ n, G.Adj v w n ∧ e = (s(v, w), n)) h₁
    (fun _ he ↦ he) fun _ _ _ ⟨w, hw, n, hn, he⟩ ⟨w', hw', n', hn', he'⟩ ↦ by
      obtain rfl := Option.mem_unique hw hw'
      obtain rfl := h₀ hn hn'
      rw [he, he']).2

/-- In a simple graph, at most `|A|` edges join `x` to `A`. -/
theorem ncard_incidentEdges_le {x : V} (h₀ : G.IsSimple) (h₁ : A.Finite) :
    (G.incidentEdges x A).ncard ≤ A.ncard :=
  (Set.finite_and_ncard_le_of_functional (S := G.incidentEdges x A)
    (fun v e ↦ ∃ n, G.Adj x v n ∧ e = (s(x, v), n)) h₁
    (fun _ he ↦ he) fun _ _ _ ⟨n, hn, he⟩ ⟨n', hn', he'⟩ ↦ by
      obtain rfl := h₀ hn hn'
      rw [he, he']).2

end Count

section ExtremallyMatched

variable [G.IsSymm] {v w : V} {n : ℕ}

/-- `E_min` also contains the earliest edges at the targets: the earliest edge at a vertex `v` of
the bi-clique, from `v` to `N_min v`, is in `G.eMin s` (for a target, it is the earliest edge at
the source `N_min v`). -/
theorem IsExtremallyMatched.mem_eMin_of_mem_union (h : G.IsExtremallyMatched s t)
    (h₀ : G.IsProper) (h₁ : v ∈ s ∪ t) (h₂ : G.earliestNeighborFn v = some w) (h₃ : G.Adj v w n) :
    (s(v, w), n) ∈ G.eMin s := by
  rcases h₁ with h₁ | h₁
  · exact mem_eMin h₁ h₂ h₃
  · -- the edge `{v, w}` seen from the source `w`, whose earliest neighbor is `v`
    rw [Sym2.eq_swap]
    exact mem_eMin (h.mem_left_of_earliestNeighborFn_eq_some h₁ h₂)
      (h.earliestNeighborFn_eq_some_symm h₀ (Or.inr h₁) h₂) h₃.symm

@[deprecated (since := "2026-10-29")]
alias IsExtremallyMatched.mem_eMin := IsExtremallyMatched.mem_eMin_of_mem_union

/-- `E_max` also contains the latest edges at the targets. -/
theorem IsExtremallyMatched.mem_eMax_of_mem_union (h : G.IsExtremallyMatched s t)
    (h₀ : G.IsProper) (h₁ : v ∈ s ∪ t) (h₂ : G.latestNeighborFn v = some w) (h₃ : G.Adj v w n) :
    (s(v, w), n) ∈ G.eMax s := by
  rcases h₁ with h₁ | h₁
  · exact mem_eMax h₁ h₂ h₃
  · -- the edge `{v, w}` seen from the source `w`, whose latest neighbor is `v`
    rw [Sym2.eq_swap]
    exact mem_eMax (h.mem_left_of_latestNeighborFn_eq_some h₁ h₂)
      (h.latestNeighborFn_eq_some_symm h₀ (Or.inr h₁) h₂) h₃.symm

@[deprecated (since := "2026-10-29")]
alias IsExtremallyMatched.mem_eMax := IsExtremallyMatched.mem_eMax_of_mem_union

end ExtremallyMatched

end TemporalGraph
