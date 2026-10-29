/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.Dismountability.Basic
public import TemporalGraph.Dismountability.Operations

/-!
# One-sided dismountability

This module formalizes the one-sided dismountability strategy recalled in SAND 2025, §4.1 (due to
Angrick et al., ESA 2024), which builds a sparse spanner of the temporal bi-clique left by
`biclique_of_not_twoHopDismountable`, together with its source-side mirror used by Baligács 2026.

Only reachability from a source part to a target part is tracked (`IsSpannerFromTo`); the
matchings `M⁻`, `M⁺` then upgrade it to temporal connectivity
(`temporallyConnected_of_reachable_of_matchings`).

## Main definitions

* `TemporalGraph.Subgraph.IsSpannerFromTo` : one-sided spanner from a source set to a target set.
* `TemporalGraph.OneSidedDismountable` : a target vertex that can delegate its
  receptions from the source to another target vertex.
* `TemporalGraph.SourceDismountable` : the time-reversed mirror, a source vertex that can delegate
  its emissions to the targets to another source vertex.
* `TemporalGraph.Subgraph.oneSidedMount` : put a dismounted vertex back, with its two
  delegation edges (for both the target and the source side).

## Main results

* `TemporalGraph.Subgraph.isSpannerFromTo_iff_of_isBicliqueWith` : in a bi-clique, a one-sided
  spanner is a subgraph in which the sources still reach the targets (either direction, through
  `IsBicliqueWith.symm`).
* `TemporalGraph.Subgraph.IsSpannerFromTo.sup`, `isSpannerFromTo_sup_of_induce` : the split
  step, one-sided spanners of the two subproblems combine by union.
* `TemporalGraph.Subgraph.oneSidedMount_size`, `ncard_edgeSet_oneSidedMount_le` : mounting adds at
  most two edges.
* `TemporalGraph.Subgraph.oneSidedDismountability` : putting a one-sided dismountable target
  back with its two delegation edges keeps a one-sided spanner.
* `TemporalGraph.Subgraph.sourceDismountability` : the mirror of `oneSidedDismountability`,
  putting a dismountable source back with its two delegation edges.
* `TemporalGraph.Subgraph.exists_earliestEdge_of_isBicliqueWith`,
  `exists_latestEdge_of_isBicliqueWith` : in a finite simple bi-clique, the earliest and latest
  edges of a vertex go to the other part.
* `TemporalGraph.Subgraph.exists_oneSidedDismountable_of_ncard_lt` : pigeonhole, a dismountable
  target exists when the target part is larger than the source part.
* `TemporalGraph.Subgraph.temporallyConnected_of_isSpannerFromTo` : a one-sided spanner from `V⁺`
  to `V⁻` containing the matchings `M⁻` and `M⁺` is temporally connected.

## References

* Carnevale, Casteigts & Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025
  (LIPIcs 330, doi:10.4230/LIPIcs.SAND.2025.6), §4.1.
* Angrick, Bals, Friedrich, Gawendowicz, Hastrich, Klodt, Lenzner, Schmidt, Skretas & Wells,
  *How to Reduce Temporal Cliques to Find Sparse Spanners*, ESA 2024 (LIPIcs 308,
  doi:10.4230/LIPIcs.ESA.2024.11, arXiv:2402.13624) — origin of the one-sided strategy.
* Baligács, *Temporal Cliques Admit Linear Spanners*, arXiv:2606.05156v1 (2026), §2.3 — the
  source side.
-/

@[expose] public section

universe u
variable {V : Type u}

namespace TemporalGraph

section Dismountable

/-- SAND 2025, §4.1: the target vertex `x ∈ t` is one-sided dismountable (relative to the source
`s`) when another target vertex `x'` has a latest edge to some `y ∈ s`, at time `n`, and `y` is
joined to `x` at a time `m ≥ n`: `x` then receives, through `x' → y → x`, everything `x'`
receives from `s`. -/
def OneSidedDismountable (G : TemporalGraph V) (s t : Set V) (x : V) : Prop :=
  x ∈ t ∧ ∃ x' ∈ t, x' ≠ x ∧ ∃ y ∈ s, ∃ n m : ℕ, G.LatestEdge x' y n ∧ G.Adj y x m ∧ n ≤ m

/-- Baligács 2026, §2.3: the source vertex `x ∈ s` is dismountable (relative to the target `t`)
when another source vertex `x'` has an earliest edge to some `y ∈ t`, at time `n`, and `y` is
joined to `x` at a time `m ≤ n`: `x` then reaches, through `x → y → x'`, everything `x'` reaches.
The mirror image of `OneSidedDismountable`, which dismounts a target. -/
def SourceDismountable (G : TemporalGraph V) (s t : Set V) (x : V) : Prop :=
  x ∈ s ∧ ∃ x' ∈ s, x' ≠ x ∧ ∃ y ∈ t, ∃ n m : ℕ, G.EarliestEdge x' y n ∧ G.Adj y x m ∧ m ≤ n

end Dismountable

namespace Subgraph

variable {G : TemporalGraph V}

section OneSided

/-! ### One-sided spanners and the split step -/

/-- SAND 2025, §4.1: `H'` is a one-sided spanner of `H` from `s` to `t`: a subgraph of `H` in
which every vertex of `s` still reaches every vertex of `t` that it reaches in `H`. -/
def IsSpannerFromTo (H' H : Subgraph G) (s t : Set V) : Prop :=
  H' ≤ H ∧ ∀ x ∈ s, ∀ y ∈ t, H.Reachable x y → H'.Reachable x y

/-- A one-sided spanner of a subgraph `K ≤ H` in which every source reaches every target is also a
one-sided spanner of `H`. -/
lemma IsSpannerFromTo.of_le {H K H' : Subgraph G} {s t : Set V}
    (h₀ : H'.IsSpannerFromTo K s t) (h₁ : K ≤ H) (h₂ : ∀ x ∈ s, ∀ y ∈ t, K.Reachable x y) :
    H'.IsSpannerFromTo H s t :=
  ⟨h₀.1.trans h₁, fun x hx y hy _ ↦ h₀.2 x hx y hy (h₂ x hx y hy)⟩

/-- In a bi-clique on `s` and `t`, every vertex of `s` reaches every vertex of `t` by a single
edge, so a one-sided spanner from `s` to `t` is just a subgraph in which `s` still reaches `t`.
With `h₀.symm`, the same statement covers the direction from `t` to `s`. -/
lemma isSpannerFromTo_iff_of_isBicliqueWith {H K : Subgraph G} {s t : Set V}
    (h₀ : H.IsBicliqueWith s t) :
    K.IsSpannerFromTo H s t ↔ K ≤ H ∧ ∀ x ∈ s, ∀ y ∈ t, K.Reachable x y :=
  ⟨fun h ↦ ⟨h.1, fun x hx y hy ↦ h.2 x hx y hy (reachable_of_isBicliqueWith h₀ hx hy)⟩,
    fun h ↦ ⟨h.1, fun x hx y hy _ ↦ h.2 x hx y hy⟩⟩

/-- SAND 2025, §4.1 (after Angrick et al., ESA 2024), split step: one-sided spanners of `H` from
`s₁` and from `s₂` to the same target `t` have a union that is a one-sided spanner from `s₁ ∪ s₂` to
`t`. -/
lemma IsSpannerFromTo.sup {H H₁ H₂ : Subgraph G} {s₁ s₂ t : Set V}
    (h₀ : H₁.IsSpannerFromTo H s₁ t) (h₁ : H₂.IsSpannerFromTo H s₂ t) :
    (H₁ ⊔ H₂).IsSpannerFromTo H (s₁ ∪ s₂) t := by
  refine ⟨sup_le h₀.1 h₁.1, ?_⟩
  rintro x (hx | hx) y hy hr
  · exact Reachable.mono (toTemporalGraph_le le_sup_left) (h₀.2 x hx y hy hr)
  · exact Reachable.mono (toTemporalGraph_le le_sup_right) (h₁.2 x hx y hy hr)

/-- SAND 2025, §4.1 (after Angrick et al., ESA 2024), split step: in a bi-clique on `s` and `t`,
one-sided spanners of the two subproblems on `s₁ ∪ t` and `s₂ ∪ t` combine, by union, into a
one-sided spanner of `H` from `s₁ ∪ s₂` to `t`. -/
lemma isSpannerFromTo_sup_of_induce {H H₁ H₂ : Subgraph G} {s t s₁ s₂ : Set V}
    (h₀ : H.IsBicliqueWith s t) (h₁ : s ∪ t ⊆ H.verts) (h₂ : s₁ ⊆ s) (h₃ : s₂ ⊆ s)
    (h₄ : H₁.IsSpannerFromTo (H.induce (s₁ ∪ t)) s₁ t)
    (h₅ : H₂.IsSpannerFromTo (H.induce (s₂ ∪ t)) s₂ t) :
    (H₁ ⊔ H₂).IsSpannerFromTo H (s₁ ∪ s₂) t := by
  have hle : ∀ s' ⊆ s, H.induce (s' ∪ t) ≤ H := fun s' hs' ↦
    induce_le_of_subset ((Set.union_subset_union_left t hs').trans h₁)
  refine (h₄.of_le (hle s₁ h₂) fun x hx y hy ↦ ?_).sup (h₅.of_le (hle s₂ h₃) fun x hx y hy ↦ ?_)
  · exact reachable_of_isBicliqueWith (isBicliqueWith_induce h₀ h₂ subset_rfl) hx hy
  · exact reachable_of_isBicliqueWith (isBicliqueWith_induce h₀ h₃ subset_rfl) hx hy

/-- Split a set into two halves of complementary size, `⌈|s| / 2⌉` and `⌊|s| / 2⌋`: used to divide
a bi-clique's source part in two before recursing (SAND 2025, §4.1, split step). Holds
unconditionally, including when `s` is infinite (both sides are then `0`, since `s.ncard = 0`). -/
lemma exists_ncard_halves {α : Type*} (s : Set α) :
    ∃ s₁ ⊆ s, s₁.ncard = (s.ncard + 1) / 2 ∧ (s \ s₁).ncard = s.ncard / 2 := by
  rcases s.finite_or_infinite with hfin | hinf
  · obtain ⟨s₁, hsub, hcard⟩ :=
      Set.exists_subset_card_eq (s := s) (n := (s.ncard + 1) / 2) (by omega)
    refine ⟨s₁, hsub, hcard, ?_⟩
    rw [Set.ncard_sdiff hsub (hfin.subset hsub), hcard]
    omega
  · have h0 : s.ncard = 0 := hinf.ncard
    exact ⟨∅, Set.empty_subset s, by simp [h0], by simp [h0]⟩

/-! ### Mounting a vertex back -/

/-- Put `x` back into `H` with the two delegation edges `y x'` (time `n`) and `y x` (time `m`).
This is the mounting step for both the target side (`oneSidedDismountability`) and the source side
(`sourceDismountability`). -/
def oneSidedMount (H : Subgraph G) [G.IsSymm] {x' y : V} {n m : ℕ}
    (hx' : x' ∈ H.verts) (hy : y ∈ H.verts) (x : V) (h₀ : G.Adj y x' n) (h₁ : G.Adj y x m) :
    G.Subgraph :=
  ((H.addVerts {x}).addEdge h₀ (by simp [hy, hx'])).addEdge h₁ (by simp [hy])

/-- `H.oneSidedMount hx' hy x h₀ h₁` has vertex set `H.verts ∪ {x}`. -/
@[simp, grind =]
lemma oneSidedMount_verts {H : Subgraph G} [G.IsSymm] {x' y x : V} {n m : ℕ}
    (hx' : x' ∈ H.verts) (hy : y ∈ H.verts) (h₀ : G.Adj y x' n) (h₁ : G.Adj y x m) :
    (H.oneSidedMount hx' hy x h₀ h₁).verts = H.verts ∪ {x} := by
  rw [oneSidedMount, addEdge_verts, addEdge_verts, addVerts_verts]

/-- `H.oneSidedMount hx' hy x h₀ h₁` is symmetric when `H` and `G` are. `oneSidedMount` is a plain
`def`, so instance resolution cannot see the `addEdge`/`addVerts` layers it is built from; this
instance unfolds it once and hands the goal back to resolution. -/
instance oneSidedMount_isSymm {H : Subgraph G} [H.IsSymm] [G.IsSymm] {x' y x : V} {n m : ℕ}
    (hx' : x' ∈ H.verts) (hy : y ∈ H.verts) (h₀ : G.Adj y x' n) (h₁ : G.Adj y x m) :
    (H.oneSidedMount hx' hy x h₀ h₁).IsSymm := by
  unfold oneSidedMount
  infer_instance

/-- `H` is a subgraph of `H.oneSidedMount hx' hy x h₀ h₁`. -/
lemma le_oneSidedMount {H : Subgraph G} [G.IsSymm] {x' y x : V} {n m : ℕ}
    (hx' : x' ∈ H.verts) (hy : y ∈ H.verts) (h₀ : G.Adj y x' n) (h₁ : G.Adj y x m) :
    H ≤ H.oneSidedMount hx' hy x h₀ h₁ := by
  unfold oneSidedMount
  have h := addVerts_le (H := H) (s := {x})
  have h' := h.trans <| addEdge_le (h := h₀) (h₁ := by simp [hy, hx'])
  exact le_trans h' addEdge_le

/-- `H.oneSidedMount hx' hy x h₀ h₁` contains the edge from `y` to `x'` at time `n`. -/
lemma oneSidedMount_adj_left (H : Subgraph G) [G.IsSymm] {x' y x : V} {n m : ℕ}
    (hx' : x' ∈ H.verts) (hy : y ∈ H.verts) (h₀ : G.Adj y x' n) (h₁ : G.Adj y x m) :
    (H.oneSidedMount hx' hy x h₀ h₁).Adj y x' n := by
  rw [oneSidedMount]
  exact addEdge_le.right addEdge_edge

/-- `H.oneSidedMount hx' hy x h₀ h₁` contains the edge from `y` to `x` at time `m`. -/
lemma oneSidedMount_adj_right (H : Subgraph G) [G.IsSymm] {x' y x : V} {n m : ℕ}
    (hx' : x' ∈ H.verts) (hy : y ∈ H.verts) (h₀ : G.Adj y x' n) (h₁ : G.Adj y x m) :
    (H.oneSidedMount hx' hy x h₀ h₁).Adj y x m := by
  rw [oneSidedMount]
  exact addEdge_edge

/-- `H.oneSidedMount hx' hy x h₀ h₁` has edge set `H.edgeSet` plus the two new edges `y x'` at `n`
and `y x` at `m`. -/
@[simp]
lemma oneSidedMount_edgeSet (H : Subgraph G) [G.IsSymm] {x' y x : V} {n m : ℕ}
    (hx' : x' ∈ H.verts) (hy : y ∈ H.verts) (h₀ : G.Adj y x' n) (h₁ : G.Adj y x m) :
    (H.oneSidedMount hx' hy x h₀ h₁).edgeSet = H.edgeSet ∪ {⟨s(y, x), m⟩, ⟨s(y, x'), n⟩} := by
  simp [oneSidedMount, addEdge_edgeSet, addVerts_edgeSet]

/-- `H.oneSidedMount hx' hy x h₀ h₁` is a subgraph of any `H₀` that contains `H`, the vertex `x`
and the two delegation edges. -/
lemma oneSidedMount_le {H H₀ : Subgraph G} [G.IsSymm] [H₀.IsSymm] {x' y x : V} {n m : ℕ}
    (hx' : x' ∈ H.verts) (hy : y ∈ H.verts) (h₀ : G.Adj y x' n) (h₁ : G.Adj y x m)
    (h₂ : H ≤ H₀) (h₃ : x ∈ H₀.verts) (h₄ : H₀.Adj y x' n) (h₅ : H₀.Adj y x m) :
    H.oneSidedMount hx' hy x h₀ h₁ ≤ H₀ := by
  apply le_iff_edgeSet_and_verts.mpr
  refine ⟨?_, ?_⟩
  · rw [H.oneSidedMount_edgeSet]
    refine Set.union_subset (edgeSet_mono h₂) ?_
    -- the two new edges `y x` and `y x'` are edges of `H₀`
    rintro p (rfl | rfl)
    · exact Adj.mem_edgeSet h₅
    · exact Adj.mem_edgeSet h₄
  · rw [H.oneSidedMount_verts]
    exact Set.union_subset h₂.left (Set.singleton_subset_iff.mpr h₃)

/-- Instance-free form of `oneSidedMount_size`: mounting `x` back onto `H` with its two
delegation edges adds at most 2 edges to `H.edgeSet`'s `Set.ncard`. -/
theorem ncard_edgeSet_oneSidedMount_le {H : Subgraph G} [G.IsSymm] {x' y x : V}
    {n m : ℕ} {hx' : x' ∈ H.verts} {hy : y ∈ H.verts} {h₀ : G.Adj y x' n} {h₁ : G.Adj y x m} :
    (H.oneSidedMount hx' hy x h₀ h₁).edgeSet.ncard ≤ H.edgeSet.ncard + 2 := by
  rw [H.oneSidedMount_edgeSet]
  have hunion := Set.ncard_union_le H.edgeSet ({⟨s(y, x), m⟩, ⟨s(y, x'), n⟩} : Set (Sym2 V × ℕ))
  have hpair := ncard_pair_le (⟨s(y, x), m⟩ : Sym2 V × ℕ) ⟨s(y, x'), n⟩
  -- `|E ∪ {e₁, e₂}| ≤ |E| + |{e₁, e₂}| ≤ |E| + 2`
  omega

/-- Mounting `x` back onto `H` with its two delegation edges adds at most 2 edges. -/
theorem oneSidedMount_size {H : Subgraph G} [G.IsSymm] {x' y x : V} {n m : ℕ}
    {hx' : x' ∈ H.verts} {hy : y ∈ H.verts} {h₀ : G.Adj y x' n} {h₁ : G.Adj y x m}
    [Fintype H.edgeSet] [Fintype (H.oneSidedMount hx' hy x h₀ h₁).edgeSet] :
    (H.oneSidedMount hx' hy x h₀ h₁).size ≤ H.size + 2 := by
  rw [size_eq_ncard, size_eq_ncard]
  exact ncard_edgeSet_oneSidedMount_le

/-! ### Correctness of dismounting -/

/-- Mount-lifting step shared by `oneSidedDismountability` and `sourceDismountability`: in a
bi-clique on `s` and `t`, a source `z ∈ s` and a target `w ∈ t`, both different from `x`, are
joined by a direct edge of `H.deleteVerts {x}`, so if `H'` is a one-sided spanner there, `z`
still reaches `w` in the mount of `x` onto `H'`. -/
private lemma reachable_oneSidedMount_of_ne {H H' : Subgraph G} [G.IsSymm]
    {s t : Set V} {x x' y z w : V} {n m : ℕ} (h₀ : H.IsBicliqueWith s t) (hz : z ∈ s) (hw : w ∈ t)
    (hzx : z ≠ x) (hwx : w ≠ x)
    (hspan : (H.deleteVerts {x}).Reachable z w → H'.Reachable z w)
    (hx' : x' ∈ H'.verts) (hy : y ∈ H'.verts) (h₁ : G.Adj y x' n) (h₂ : G.Adj y x m) :
    (H'.oneSidedMount hx' hy x h₁ h₂).Reachable z w := by
  obtain ⟨k, hadj⟩ := h₀.adj_of_mem hz hw
  -- the bi-clique edge `z w` survives the deletion of `x`
  have hdel : (H.deleteVerts {x}).Adj z w k := by
    simp only [deleteVerts, induce_Adj, Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨⟨H.edge_vert hadj, hzx⟩, ⟨H.edge_vert' hadj, hwx⟩, hadj⟩
  have hreach : H'.Reachable z w := hspan (NonemptyTemporalWalk.reachable (.single hdel))
  exact Reachable.mono (toTemporalGraph_le (le_oneSidedMount hx' hy h₁ h₂)) hreach

/-- SAND 2025, §4.1 (after Angrick et al., ESA 2024): correctness of one-sided dismounting. In a
bi-clique on `s` and `t`, if `x` is one-sided dismountable through `x'` and `y`, and `H'` is a
one-sided spanner from `s` to `t \ {x}` of `H` without `x`, then putting `x` back with the edges
`y x'` and `y x` gives a one-sided spanner from `s` to `t` of `H`. -/
theorem oneSidedDismountability {H H' : Subgraph G} [G.IsSymm] [H.IsSymm] [H'.IsSymm]
    {s t : Set V} {x x' y : V} {n m : ℕ}
    (h₀ : H.IsBicliqueWith s t) (h₁ : x ∈ t) (h₂ : x' ∈ t) (h₃ : x' ≠ x)
    (h₄ : H.LatestEdge x' y n) (h₅ : H.Adj y x m) (h₆ : n ≤ m)
    (h₇ : H'.IsSpannerFromTo (H.deleteVerts {x}) s (t \ {x}))
    (hx' : x' ∈ H'.verts) (hy : y ∈ H'.verts) :
    (H'.oneSidedMount hx' hy x (H.adj_sub h₄.1).symm (H.adj_sub h₅)).IsSpannerFromTo H s t := by
  have hyx' : G.Adj y x' n := (H.adj_sub h₄.1).symm
  have hyx : G.Adj y x m := H.adj_sub h₅
  set M := H'.oneSidedMount hx' hy x hyx' hyx
  have hMH : M ≤ H :=
    oneSidedMount_le hx' hy _ _ (h₇.1.trans deleteVerts_le) (H.edge_vert' h₅) h₄.1.symm h₅
  refine ⟨hMH, fun z hz w hw hr ↦ ?_⟩
  -- a source `z` is not the target `x`
  have hzx : z ≠ x := fun he ↦ Set.disjoint_left.mp h₀.isBipartiteWith.disjoint hz (he ▸ h₁)
  -- every target `w' ≠ x` stays reachable from `z`
  have key : ∀ w' ∈ t \ {x}, M.Reachable z w' := fun w' hw' ↦
    reachable_oneSidedMount_of_ne h₀ hz hw'.1 hzx hw'.2 (h₇.2 z hz w' hw') hx' hy hyx' hyx
  by_cases hwx : w = x
  · -- `w = x`: reach `x'` first (it survives the dismount), then extend through `y x`, as
    -- `x'`'s edge to `y` is still the latest one in `M` (it was in `H`, which contains `M`)
    subst hwx
    have hMx'y : M.Adj x' y n := (oneSidedMount_adj_left H' hx' hy hyx' hyx).symm
    have hML : M.LatestEdge x' y n := latestEdge_of_ge hMH h₄ hMx'y
    exact TemporalGraph.reachable_of_extended_latestEdge hML
      (oneSidedMount_adj_right H' hx' hy hyx' hyx) h₆ z (key x' ⟨h₂, h₃⟩)
  · exact key w ⟨hw, hwx⟩

/-- Baligács 2026, §2.3: correctness of source dismounting, the mirror of
`oneSidedDismountability`. In a bi-clique on `s` and `t`, if `x` is a dismountable source through
`x'` and `y`, and `H'` is a one-sided spanner from `s \ {x}` to `t` of `H` without `x`, then
putting `x` back with the edges `y x'` and `y x` gives a one-sided spanner from `s` to `t` of
`H`. -/
theorem sourceDismountability {H H' : Subgraph G} [G.IsSymm] [H.IsSymm] [H'.IsSymm]
    {s t : Set V} {x x' y : V} {n m : ℕ}
    (h₀ : H.IsBicliqueWith s t) (h₁ : x ∈ s) (h₂ : x' ∈ s) (h₃ : x' ≠ x)
    (h₄ : H.EarliestEdge x' y n) (h₅ : H.Adj y x m) (h₆ : m ≤ n)
    (h₇ : H'.IsSpannerFromTo (H.deleteVerts {x}) (s \ {x}) t)
    (hx' : x' ∈ H'.verts) (hy : y ∈ H'.verts) :
    (H'.oneSidedMount hx' hy x (H.adj_sub h₄.1).symm (H.adj_sub h₅)).IsSpannerFromTo H s t := by
  have hyx' : G.Adj y x' n := (H.adj_sub h₄.1).symm
  have hyx : G.Adj y x m := H.adj_sub h₅
  set M := H'.oneSidedMount hx' hy x hyx' hyx
  have hMH : M ≤ H :=
    oneSidedMount_le hx' hy _ _ (h₇.1.trans deleteVerts_le) (H.edge_vert' h₅) h₄.1.symm h₅
  refine ⟨hMH, fun z hz w hw hr ↦ ?_⟩
  -- a target `w` is not the source `x`
  have hwx : w ≠ x := fun he ↦ Set.disjoint_left.mp h₀.isBipartiteWith.disjoint h₁ (he ▸ hw)
  -- every source `z' ≠ x` keeps reaching `w`
  have key : ∀ z' ∈ s \ {x}, M.Reachable z' w := fun z' hz' ↦
    reachable_oneSidedMount_of_ne h₀ hz'.1 hw hz'.2 hwx (h₇.2 z' hz' w hw) hx' hy hyx' hyx
  by_cases hzx : z = x
  · -- `z = x`: reach `w` from `x'` first (it survives the dismount), then prepend `x → y → x'`,
    -- as `x'`'s edge to `y` is still the earliest one in `M` (it was in `H`, which contains `M`)
    subst hzx
    have hMx'y : M.Adj x' y n := (oneSidedMount_adj_left H' hx' hy hyx' hyx).symm
    have hME : M.EarliestEdge x' y n := earliestEdge_of_ge hMH h₄ hMx'y
    exact TemporalGraph.reachable_of_extended_earliestEdge hME
      (oneSidedMount_adj_right H' hx' hy hyx' hyx).symm h₆ w (key x' ⟨h₂, h₃⟩)
  · exact key z ⟨hz, hzx⟩

/-! ### Pigeonhole: a dismountable target exists -/

/-- In a finite simple bi-clique on `s` and `t` with `s` nonempty, every vertex of `t` has a
latest edge, and it goes to `s`. -/
lemma exists_latestEdge_of_isBicliqueWith {H : Subgraph G} [Finite H.verts] [H.IsSymm]
    {s t : Set V} {x : V}
    (h₀ : H.IsSimple) (h₁ : H.IsBicliqueWith s t) (h₂ : s.Nonempty) (h₃ : x ∈ t) :
    ∃ y ∈ s, ∃ n, H.LatestEdge x y n := by
  obtain ⟨z, hz⟩ := h₂
  obtain ⟨k, hadj⟩ := h₁.adj_of_mem hz h₃
  have hin : ((z, k) : V × ℕ) ∈ H.incidenceSet x := hadj.symm
  have hne : (H.incidenceSet x).Nonempty := ⟨(z, k), hin⟩
  have hfin : (H.incidenceSet x).Finite := finite_incidenceSet_of_finite_simple h₀ x
  obtain ⟨y, n, hlat⟩ := latestEdge_exists_of_nonempty_finite_incidenceSet hne hfin
  exact ⟨y, h₁.isBipartiteWith.mem_of_mem_adj' h₃ hlat.1, n, hlat⟩

/-- In a finite simple bi-clique on `s` and `t` with `s` nonempty, every vertex of `t` has an
earliest edge, and it goes to `s` (for a vertex of `s`, apply it to `h₁.symm`). -/
lemma exists_earliestEdge_of_isBicliqueWith {H : Subgraph G} [Finite H.verts] [H.IsSymm]
    {s t : Set V} {x : V}
    (h₀ : H.IsSimple) (h₁ : H.IsBicliqueWith s t) (h₂ : s.Nonempty) (h₃ : x ∈ t) :
    ∃ y ∈ s, ∃ n, H.EarliestEdge x y n := by
  obtain ⟨z, hz⟩ := h₂
  obtain ⟨k, hadj⟩ := h₁.adj_of_mem hz h₃
  have hne : (H.incidenceSet x).Nonempty := ⟨(z, k), hadj.symm⟩
  have hfin : (H.incidenceSet x).Finite := finite_incidenceSet_of_finite_simple h₀ x
  obtain ⟨y, n, hear⟩ := earliestEdge_exists_of_nonempty_finite_incidenceSet hne hfin
  exact ⟨y, h₁.isBipartiteWith.mem_of_mem_adj' h₃ hear.1, n, hear⟩

/-- SAND 2025, §4.1 (after Angrick et al., ESA 2024), pigeonhole: in a finite simple bi-clique on
`s` and `t` with `s` nonempty and `|s| < |t|`, two vertices of `t` share their latest neighbor in
`s`, so some vertex of `t` is one-sided dismountable. -/
lemma exists_oneSidedDismountable_of_ncard_lt {H : Subgraph G} [Finite H.verts] [H.IsSymm]
    {s t : Set V}
    (h₀ : H.IsSimple) (h₁ : H.IsBicliqueWith s t) (h₂ : s.Nonempty)
    (h₃ : s.ncard < t.ncard) :
    ∃ x, H.OneSidedDismountable s t x := by
  classical
  -- `choose!` needs `V` to be inhabited, as `s` is nonempty
  have : Nonempty V := ⟨h₂.choose⟩
  have hex : ∀ x ∈ t, ∃ y ∈ s, ∃ n, H.LatestEdge x y n :=
    fun x hx ↦ exists_latestEdge_of_isBicliqueWith h₀ h₁ h₂ hx
  choose! f hfs n hn using hex
  have ht0 : t.ncard ≠ 0 := ((Nat.zero_le s.ncard).trans_lt h₃).ne'
  obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero ht0
  -- `s` is finite, being contained in `H.verts`
  have hsub : s ⊆ H.verts := fun v hv ↦ by
    obtain ⟨k, hadj⟩ := h₁.adj_of_mem hv hw
    exact H.edge_vert hadj
  have hsFin : s.Finite := (Set.toFinite H.verts).subset hsub
  -- pigeonhole: `|s| < |t|`, so two distinct `a`, `b` in `t` have the same latest neighbor `f a`
  obtain ⟨a, ha, b, hb, hab, hfab⟩ :=
    Set.exists_ne_map_eq_of_ncard_lt_of_maps_to h₃ hfs hsFin
  have hnb' : H.LatestEdge b (f a) (n b) := by
    rw [hfab]
    exact hn b hb
  -- the one with the earlier latest edge is dismountable, delegating to the other
  rcases le_total (n a) (n b) with hle | hle
  · exact ⟨b, hb, a, ha, hab, f a, hfs a ha, n a, n b, hn a ha, hnb'.1.symm, hle⟩
  · exact ⟨a, ha, b, hb, hab.symm, f a, hfs a ha, n b, n a, hnb', (hn a ha).1.symm, hle⟩

/-! ### Assembly: temporal connectivity -/

/-- SAND 2025, §4.1 (after Corollary 4.1): in the bi-clique left by a clique that is not `{1,2}`-hop
dismountable, a one-sided spanner from `V⁺` to `V⁻` that contains the matchings `M⁻` and `M⁺` is
temporally connected on `H.verts`. -/
theorem temporallyConnected_of_isSpannerFromTo {H S : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm] [S.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable)
    (h₄ : S.IsSpannerFromTo (H.between H.vminus H.vplus) H.vplus H.vminus)
    (h₅ : ∀ v ∈ H.vplus, ∀ a n, H.EarliestEdge v a n → S.Adj v a n)
    (h₆ : ∀ b ∈ H.vminus, ∀ y n, H.LatestEdge b y n → S.Adj b y n) :
    S.TemporallyConnected H.verts := by
  have hSH : S ≤ H := h₄.1.trans between_le
  have hbc := biclique_of_not_twoHopDismountable h₁ h₃
  have hverts : H.verts = H.vplus ∪ H.vminus := by
    rw [← vunion_eq_univ, vzero_empty_of_not_twoHopDismountable h₀ h₁ h₂ h₃, Set.union_empty,
      Set.union_comm]
  rw [hverts]
  refine temporallyConnected_of_reachable_of_matchings (G := S.toTemporalGraph) ?_ ?_ ?_
  · -- `M⁻`: every vertex of `V⁻` is the end of the earliest edge of a vertex of `V⁺`
    intro a ha
    obtain ⟨⟨v, n⟩, ⟨hv, he⟩, -⟩ := existsUnique_vplus_earliestEdge h₀ h₁ h₂ h₃ a ha
    exact ⟨v, hv, n, earliestEdge_of_ge hSH he (h₅ v hv a n he)⟩
  · -- `M⁺`: every vertex of `V⁺` is the end of the latest edge of a vertex of `V⁻`
    intro y hy
    obtain ⟨⟨b, n⟩, ⟨hb, hl⟩, -⟩ := existsUnique_vminus_latestEdge h₀ h₁ h₂ h₃ y hy
    exact ⟨b, hb, n, latestEdge_of_ge hSH hl (h₆ b hb y n hl)⟩
  · -- `V⁺ → V⁻`: a direct edge of the bi-clique, kept by the one-sided spanner
    intro x hx y hy
    obtain ⟨n, hn⟩ := hbc.adj_of_mem' hy hx
    exact h₄.2 x hx y hy (NonemptyTemporalWalk.reachable (.single hn))

end OneSided

end Subgraph

end TemporalGraph
