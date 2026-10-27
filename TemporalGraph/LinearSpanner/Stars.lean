/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.LinearSpanner.ExtremallyMatched

/-!
# Stars of an extremally matched bi-clique: definitions

The edge sets and vertex predicates of Baligács 2026, §§3–4, on a temporal bi-clique with sources
`s` and targets `t`. The results about them are in `LinearSpanner/SimpleStar.lean` (§3,
Observation 9) and `LinearSpanner/ExtendedStar.lean` (§4, Lemmas 13–16).

**Labelings without indices.** The paper numbers the vertices along the order induced by a center
(Definition 7). For a source center `c`, the targets are sorted by the times of their edges to
`c`, and the `i`-th source is the earliest neighbor `N_min` of the `i`-th target. We never build
these indices: "`j ≤ i`" is a comparison of arc times at the center. For a target `u` the index is
read on `G.arcTime c u`; for a source `v` on `G.arcTime c w` with `w = N_min v`. A cut at `k`
(Definition 8) is a threshold time `τ`. For a target center the order is by decreasing time.

**`Option` values.** `arcTime` and `earliestNeighborFn` are `Option`-valued. Every comparison is
stated through the values, `∃ k ∈ G.arcTime c u, k ≤ τ`, which is false on `none`, never through
the order of `Option` (in which `none` is the least element). In an extremally matched bi-clique all
these values exist, so nothing is lost.

## Main definitions

* `TemporalGraph.eMin`, `TemporalGraph.eMax` : the matchings `E_min` and `E_max`.
* `TemporalGraph.incidentEdges` : the edges from a vertex to a set.
* `TemporalGraph.simpleStar` : Definition 8 (i), the simple star `Star(c)`.
* `TemporalGraph.IsCutCrossing` : Definition 8 (ii), the `m`-hop-`k`-cut-crossing sources.
* `TemporalGraph.IsSourceExtendTarget`, `TemporalGraph.IsTargetExtendSource` : the extend index of
  Definition 12.
* `TemporalGraph.extStarSource`, `TemporalGraph.extStarTarget` : Definition 12, the extended stars
  `Ext(c)` from a source and from a target.

## Main results

* `TemporalGraph.eMin_subset_edgeSet`, … : all these sets consist of edges of the graph, with no
  hypothesis (their times are given by `arcTime`).
* `TemporalGraph.ncard_eMin_le`, `ncard_eMax_le`, `ncard_incidentEdges_le` : at most one edge per
  vertex of the indexing set (through `finite_and_ncard_le_of_functional`).
* `TemporalGraph.IsExtremallyMatched.mem_eMin`, `mem_eMax` : `E_min` and `E_max` also contain the
  earliest and latest edges at the targets.

## References

* Júlia Baligács, *Temporal Cliques Admit Linear Spanners*, arXiv:2606.05156v1 (2026), §§3–4.
-/

@[expose] public section

universe u

namespace TemporalGraph

variable {V : Type u} {G : TemporalGraph V} {s t A : Set V}

section Definitions

/-- The edges `{v, N_min(v)}` for `v ∈ A`, at their times. For an extremally matched bi-clique,
`G.eMin s` is the matching `E_min` of Baligács 2026, §2.3. -/
def eMin (G : TemporalGraph V) (A : Set V) : Set (Sym2 V × ℕ) :=
  {e | ∃ v ∈ A, ∃ w ∈ G.earliestNeighborFn v, ∃ n ∈ G.arcTime v w, e = (s(v, w), n)}

/-- The edges `{v, N_max(v)}` for `v ∈ A`, at their times. For an extremally matched bi-clique,
`G.eMax s` is the matching `E_max` of Baligács 2026, §2.3. -/
def eMax (G : TemporalGraph V) (A : Set V) : Set (Sym2 V × ℕ) :=
  {e | ∃ v ∈ A, ∃ w ∈ G.latestNeighborFn v, ∃ n ∈ G.arcTime v w, e = (s(v, w), n)}

/-- The edges from `x` to the vertices of `A`, at their times. -/
def incidentEdges (G : TemporalGraph V) (x : V) (A : Set V) : Set (Sym2 V × ℕ) :=
  {e | ∃ v ∈ A, ∃ n ∈ G.arcTime x v, e = (s(x, v), n)}

/-- Baligács 2026, Definition 8 (i): the simple star `Star(c)` from the source `c` consists of
`E_min` and of all the edges at `c`. -/
def simpleStar (G : TemporalGraph V) (s t : Set V) (c : V) : Set (Sym2 V × ℕ) :=
  G.eMin s ∪ G.incidentEdges c t

/-- Baligács 2026, Definition 8 (ii), with the cut `k` given by the threshold time `τ`: in the
`c`-ordered labeling, the source `v = sᵢ` is `m`-hop-`k`-cut-crossing when `i > k` and some
temporal walk of length at most `m + 1` starts at `v` and ends with the edge `{t_j, c}` for some
`j ≤ k`. The walk is split into its part from `v` to `t_j = N_min(s_j)`, of length at most `m`,
and the final edge to `c`, which must come no earlier. -/
def IsCutCrossing (G : TemporalGraph V) (s : Set V) (c : V) (τ m : ℕ) (v : V) : Prop :=
  (∃ u ∈ G.earliestNeighborFn v, ∃ k ∈ G.arcTime c u, τ < k) ∧
    ∃ w ∈ s, ∃ u ∈ G.earliestNeighborFn w, (∃ k ∈ G.arcTime c u, k ≤ τ) ∧
      ∃ n n' : ℕ, ∃ p : G.TemporalWalk v n u n', p.length ≤ m ∧ ∃ k ∈ G.arcTime u c, n' ≤ k

/-- Baligács 2026, Definition 12 (a): for the source center `c`, the extend index of the source
`v` is the target `u = t_{ind(v)}`: the last target, in the `c`-ordered labeling, whose edge to
`v` comes after its edge to `c`. -/
def IsSourceExtendTarget (G : TemporalGraph V) (t : Set V) (c v u : V) : Prop :=
  u ∈ t ∧ (∃ a ∈ G.arcTime u c, ∃ b ∈ G.arcTime u v, a < b) ∧
    ∀ u' ∈ t, (∃ a ∈ G.arcTime u' c, ∃ b ∈ G.arcTime u' v, a < b) →
      ∃ a ∈ G.arcTime c u', ∃ b ∈ G.arcTime c u, a ≤ b

/-- Baligács 2026, Definition 12 (b): for the target center `c`, the extend index of the target
`v` is the source `u = s_{ind(v)}`: the last source, in the `c`-ordered labeling (by decreasing
time at `c`), whose edge to `v` comes before its edge to `c`. -/
def IsTargetExtendSource (G : TemporalGraph V) (s : Set V) (c v u : V) : Prop :=
  u ∈ s ∧ (∃ a ∈ G.arcTime u v, ∃ b ∈ G.arcTime u c, a < b) ∧
    ∀ u' ∈ s, (∃ a ∈ G.arcTime u' v, ∃ b ∈ G.arcTime u' c, a < b) →
      ∃ a ∈ G.arcTime c u, ∃ b ∈ G.arcTime c u', a ≤ b

/-- Baligács 2026, Definition 12 (a): the extend edges of `Ext(c)`, joining each source to the
target at its extend index (when it has one). -/
def sourceExtendEdges (G : TemporalGraph V) (s t : Set V) (c : V) : Set (Sym2 V × ℕ) :=
  {e | ∃ v ∈ s, ∃ u, G.IsSourceExtendTarget t c v u ∧ ∃ n ∈ G.arcTime v u, e = (s(v, u), n)}

/-- Baligács 2026, Definition 12 (b): the extend edges of `Ext(c)`, joining each target to the
source at its extend index (when it has one). -/
def targetExtendEdges (G : TemporalGraph V) (s t : Set V) (c : V) : Set (Sym2 V × ℕ) :=
  {e | ∃ v ∈ t, ∃ u, G.IsTargetExtendSource s c v u ∧ ∃ n ∈ G.arcTime u v, e = (s(u, v), n)}

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
    (h₂ : G.arcTime v w = some n) : (s(v, w), n) ∈ G.eMin A :=
  ⟨v, h₀, w, h₁, n, h₂, rfl⟩

/-- The edge from `v ∈ A` to `N_max v` is in `G.eMax A`. -/
theorem mem_eMax (h₀ : v ∈ A) (h₁ : G.latestNeighborFn v = some w)
    (h₂ : G.arcTime v w = some n) : (s(v, w), n) ∈ G.eMax A :=
  ⟨v, h₀, w, h₁, n, h₂, rfl⟩

/-- The edge from `x` to `v ∈ A` is in `G.incidentEdges x A`. -/
theorem mem_incidentEdges (h₀ : v ∈ A) (h₁ : G.arcTime x v = some n) :
    (s(x, v), n) ∈ G.incidentEdges x A :=
  ⟨v, h₀, n, h₁, rfl⟩

end Membership

section Subset

/-- An edge whose time is given by `arcTime` is an edge of the graph. -/
private theorem mem_edgeSet_of_arcTime {u v : V} {n : ℕ} (h₀ : G.arcTime u v = some n) :
    (s(u, v), n) ∈ G.edgeSet :=
  ⟨u, v, rfl, adj_of_arcTime_eq_some h₀⟩

/-- `G.eMin A` consists of edges of `G`. -/
theorem eMin_subset_edgeSet : G.eMin A ⊆ G.edgeSet := by
  rintro _ ⟨v, -, w, -, n, h₀, rfl⟩
  exact mem_edgeSet_of_arcTime h₀

/-- `G.eMax A` consists of edges of `G`. -/
theorem eMax_subset_edgeSet : G.eMax A ⊆ G.edgeSet := by
  rintro _ ⟨v, -, w, -, n, h₀, rfl⟩
  exact mem_edgeSet_of_arcTime h₀

/-- `G.incidentEdges x A` consists of edges of `G`. -/
theorem incidentEdges_subset_edgeSet {x : V} : G.incidentEdges x A ⊆ G.edgeSet := by
  rintro _ ⟨v, -, n, h₀, rfl⟩
  exact mem_edgeSet_of_arcTime h₀

/-- The extend edges of `Ext(c)`, `c` a source, are edges of `G`. -/
theorem sourceExtendEdges_subset_edgeSet {c : V} : G.sourceExtendEdges s t c ⊆ G.edgeSet := by
  rintro _ ⟨v, -, u, -, n, h₀, rfl⟩
  exact mem_edgeSet_of_arcTime h₀

/-- The extend edges of `Ext(c)`, `c` a target, are edges of `G`. -/
theorem targetExtendEdges_subset_edgeSet {c : V} : G.targetExtendEdges s t c ⊆ G.edgeSet := by
  rintro _ ⟨v, -, u, -, n, h₀, rfl⟩
  exact mem_edgeSet_of_arcTime h₀

/-- The simple star consists of edges of `G`. -/
theorem simpleStar_subset_edgeSet {c : V} : G.simpleStar s t c ⊆ G.edgeSet :=
  Set.union_subset eMin_subset_edgeSet incidentEdges_subset_edgeSet

/-- The extended star from a source consists of edges of `G`. -/
theorem extStarSource_subset_edgeSet {c : V} : G.extStarSource s t c ⊆ G.edgeSet :=
  Set.union_subset (Set.union_subset (Set.union_subset eMin_subset_edgeSet eMax_subset_edgeSet)
    incidentEdges_subset_edgeSet) sourceExtendEdges_subset_edgeSet

/-- The extended star from a target consists of edges of `G`. -/
theorem extStarTarget_subset_edgeSet {c : V} : G.extStarTarget s t c ⊆ G.edgeSet :=
  Set.union_subset (Set.union_subset (Set.union_subset eMin_subset_edgeSet eMax_subset_edgeSet)
    incidentEdges_subset_edgeSet) targetExtendEdges_subset_edgeSet

end Subset

section Count

/-- A set `S` in which each element is related by a functional relation `R` to a vertex of a
finite set `A` is finite, with at most `|A|` elements: at most one element per vertex. -/
theorem finite_and_ncard_le_of_functional {α : Type*} {S : Set α} (R : V → α → Prop)
    (h₀ : A.Finite) (h₁ : ∀ e ∈ S, ∃ v ∈ A, R v e) (h₂ : ∀ v e e', R v e → R v e' → e = e') :
    S.Finite ∧ S.ncard ≤ A.ncard := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
  · simp
  obtain ⟨v₀, -⟩ := h₁ e₀ he₀
  have : Nonempty V := ⟨v₀⟩
  -- choose a related vertex of `A` for each element of `S`; this is an injection
  choose! f hfA hfR using h₁
  have h₃ : S.InjOn f := fun e he e' he' h ↦ h₂ (f e) e e' (hfR e he) (h ▸ hfR e' he')
  exact ⟨Set.Finite.of_injOn hfA h₃ h₀, Set.ncard_le_ncard_of_injOn f hfA h₃ h₀⟩

/-- At most one edge of `E_min` per vertex of `A`: `N_min` and `arcTime` are functions. -/
theorem ncard_eMin_le (h₀ : A.Finite) : (G.eMin A).ncard ≤ A.ncard :=
  (finite_and_ncard_le_of_functional (S := G.eMin A)
    (fun v e ↦ ∃ w ∈ G.earliestNeighborFn v, ∃ n ∈ G.arcTime v w, e = (s(v, w), n)) h₀
    (fun _ ⟨v, hv, hr⟩ ↦ ⟨v, hv, hr⟩) fun _ _ _ ⟨w, hw, n, hn, he⟩ ⟨w', hw', n', hn', he'⟩ ↦ by
      obtain rfl := Option.mem_unique hw hw'
      obtain rfl := Option.mem_unique hn hn'
      rw [he, he']).2

/-- At most one edge of `E_max` per vertex of `A`. -/
theorem ncard_eMax_le (h₀ : A.Finite) : (G.eMax A).ncard ≤ A.ncard :=
  (finite_and_ncard_le_of_functional (S := G.eMax A)
    (fun v e ↦ ∃ w ∈ G.latestNeighborFn v, ∃ n ∈ G.arcTime v w, e = (s(v, w), n)) h₀
    (fun _ ⟨v, hv, hr⟩ ↦ ⟨v, hv, hr⟩) fun _ _ _ ⟨w, hw, n, hn, he⟩ ⟨w', hw', n', hn', he'⟩ ↦ by
      obtain rfl := Option.mem_unique hw hw'
      obtain rfl := Option.mem_unique hn hn'
      rw [he, he']).2

/-- At most `|A|` edges join `x` to `A`. -/
theorem ncard_incidentEdges_le {x : V} (h₀ : A.Finite) : (G.incidentEdges x A).ncard ≤ A.ncard :=
  (finite_and_ncard_le_of_functional (S := G.incidentEdges x A)
    (fun v e ↦ ∃ n ∈ G.arcTime x v, e = (s(x, v), n)) h₀
    (fun _ ⟨v, hv, hr⟩ ↦ ⟨v, hv, hr⟩) fun _ _ _ ⟨n, hn, he⟩ ⟨n', hn', he'⟩ ↦ by
      obtain rfl := Option.mem_unique hn hn'
      rw [he, he']).2

end Count

section ExtremallyMatched

variable [G.IsSymm] {v w : V} {n : ℕ}

/-- `E_min` also contains the earliest edges at the targets: the earliest edge at a vertex `v` of
the bi-clique, from `v` to `N_min v`, is in `G.eMin s` (for a target, it is the earliest edge at
the source `N_min v`). -/
theorem IsExtremallyMatched.mem_eMin (h : G.IsExtremallyMatched s t) (h₀ : G.IsSimple)
    (h₁ : G.IsProper) (h₂ : v ∈ s ∪ t) (h₃ : G.earliestNeighborFn v = some w)
    (h₄ : G.arcTime v w = some n) : (s(v, w), n) ∈ G.eMin s := by
  rcases h₂ with h₂ | h₂
  · exact TemporalGraph.mem_eMin h₂ h₃ h₄
  · -- the edge `{v, w}` seen from the source `w`, whose earliest neighbor is `v`
    rw [Sym2.eq_swap]
    exact TemporalGraph.mem_eMin (h.mem_left_of_earliestNeighborFn_eq_some h₂ h₃)
      (h.earliestNeighborFn_eq_some_symm h₁ (Or.inr h₂) h₃) (arcTime_comm h₀ v w ▸ h₄)

/-- `E_max` also contains the latest edges at the targets. -/
theorem IsExtremallyMatched.mem_eMax (h : G.IsExtremallyMatched s t) (h₀ : G.IsSimple)
    (h₁ : G.IsProper) (h₂ : v ∈ s ∪ t) (h₃ : G.latestNeighborFn v = some w)
    (h₄ : G.arcTime v w = some n) : (s(v, w), n) ∈ G.eMax s := by
  rcases h₂ with h₂ | h₂
  · exact TemporalGraph.mem_eMax h₂ h₃ h₄
  · -- the edge `{v, w}` seen from the source `w`, whose latest neighbor is `v`
    rw [Sym2.eq_swap]
    exact TemporalGraph.mem_eMax (h.mem_left_of_latestNeighborFn_eq_some h₂ h₃)
      (h.latestNeighborFn_eq_some_symm h₁ (Or.inr h₂) h₃) (arcTime_comm h₀ v w ▸ h₄)

end ExtremallyMatched

end TemporalGraph
