/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Dismountability.Basic
import TemporalGraph.Dismountability.Operations

/-!
# One-sided dismountability

This module formalizes the one-sided dismountability strategy recalled in SAND 2025, §4.1 (due to
Angrick et al.), which builds a sparse spanner of the temporal bi-clique left by
`biclique_of_not_twoHopDismountable`. Only reachability from a source part to a target part is
tracked (`IsSpannerFromTo`); the matchings `M⁻`, `M⁺` then upgrade it to temporal connectivity
(`temporallyConnected_of_reachable_of_matchings`).

## Main definitions

* `TemporalGraph.Subgraph.IsSpannerFromTo` : one-sided spanner from a source set to a target set.
* `TemporalGraph.Subgraph.OneSidedDismountable` : a target vertex that can delegate its
  receptions from the source to another target vertex.
* `TemporalGraph.Subgraph.oneSidedMount` : put a dismounted target vertex back, with its two
  delegation edges.

## Main results

* `TemporalGraph.Subgraph.IsSpannerFromTo.sup` : the split step, one-sided spanners from two
  sources combine by union.

## References

* Carnevale, Casteigts & Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025
  (LIPIcs 330, doi:10.4230/LIPIcs.SAND.2025.6), §4.1.
-/

universe u
variable {V : Type u}

namespace TemporalGraph

namespace Subgraph

variable {G : TemporalGraph V}

section OneSided

/-- SAND 2025, §4.1: `H'` is a one-sided spanner of `H` from `s` to `t`: a subgraph of `H` in
which every vertex of `s` still reaches every vertex of `t` that it reaches in `H`. -/
def IsSpannerFromTo (H' H : Subgraph G) (s t : Set V) : Prop :=
  H' ≤ H ∧ ∀ x ∈ s, ∀ y ∈ t, H.Reachable x y → H'.Reachable x y

/-- SAND 2025, §4.1: the target vertex `x ∈ t` is one-sided dismountable (relative to the source
`s`) when another target vertex `x'` has a latest edge to some `y ∈ s`, at time `n`, and `y` is
joined to `x` at a time `m ≥ n`: `x` then receives, through `x' → y → x`, everything `x'`
receives from `s`. -/
def OneSidedDismountable (H : Subgraph G) (s t : Set V) (x : V) : Prop :=
  x ∈ t ∧ ∃ x' ∈ t, x' ≠ x ∧ ∃ y ∈ s, ∃ n m : ℕ, H.LatestEdge x' y n ∧ H.Adj y x m ∧ n ≤ m

/-- Put `x` back into `H` with the two delegation edges `y x'` (time `n`) and `y x` (time `m`). -/
def oneSidedMount (H : Subgraph G) [G.IsSymm] {x' y : V} {n m : ℕ}
    (hx' : x' ∈ H.verts) (hy : y ∈ H.verts) (x : V) (h₀ : G.Adj y x' n) (h₁ : G.Adj y x m) :
    G.Subgraph :=
  ((H.addVerts {x}).addEdge h₀ (by simp [hy, hx'])).addEdge h₁ (by simp [hy])

/-- SAND 2025, §4.1 (split): one-sided spanners of `H` from `s₁` and from `s₂` to the same
target `t` have a union that is a one-sided spanner from `s₁ ∪ s₂` to `t`. -/
lemma IsSpannerFromTo.sup {H H₁ H₂ : Subgraph G} {s₁ s₂ t : Set V}
    (h₀ : H₁.IsSpannerFromTo H s₁ t) (h₁ : H₂.IsSpannerFromTo H s₂ t) :
    (H₁ ⊔ H₂).IsSpannerFromTo H (s₁ ∪ s₂) t := by
  refine ⟨sup_le h₀.1 h₁.1, ?_⟩
  rintro x (hx | hx) y hy hr
  · exact Reachable.mono (toTemporalGraph_le le_sup_left) (h₀.2 x hx y hy hr)
  · exact Reachable.mono (toTemporalGraph_le le_sup_right) (h₁.2 x hx y hy hr)

/-- SAND 2025, §4.1: in the bi-clique left by a clique that is not `{1,2}`-hop dismountable, a
one-sided spanner from `V⁺` to `V⁻` that contains the matchings `M⁻` and `M⁺` is temporally
connected on `H.verts`. -/
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
    exact h₄.2 x hx y hy (reachable_of_nonempty_NonemptyTemporalWalk ⟨n, n, ⟨.Single hn⟩⟩)

end OneSided

end Subgraph

end TemporalGraph
