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

end OneSided

end Subgraph

end TemporalGraph
