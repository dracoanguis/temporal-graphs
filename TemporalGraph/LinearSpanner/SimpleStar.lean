/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.LinearSpanner.Stars

import Mathlib.Data.Set.Card.Arithmetic

/-!
# The simple star of an extremally matched bi-clique

Baligács 2026, §3, Observation 9. On an extremally matched bi-clique with sources `s` and targets
`t`, a source center `c` and a threshold time `τ` (the cut `k` of the paper), the simple star
`Star(c)` together with a set `E` of at most `m · |S_cross|` edges makes every source that is early
(its `N_min` is reached by `c` by time `τ`) or `m`-hop-`τ`-cut-crossing reach every target that `c`
reaches at time `τ` or later.

## Main results

* `TemporalGraph.IsExtremallyMatched.exists_reachable_simpleStar` : Baligács 2026, Observation 9.

## References

* Júlia Baligács, *Temporal Cliques Admit Linear Spanners*, arXiv:2606.05156v1 (2026), §3.
-/

@[expose] public section

universe u

namespace TemporalGraph

variable {V : Type u} {G : TemporalGraph V} {s t : Set V}

namespace IsExtremallyMatched

variable {c u w x y : V}

/-- The end of the walks of Baligács 2026, Observation 9: a walk that reaches `u = N_min w` no
later than the edge `{u, c}` continues through `c` to every target `y` whose edge to `c` is not
earlier than that of `u`, using only edges at `c`. -/
theorem reachable_of_reachableBefore_earliestNeighborFn {H : Subgraph G} [H.IsSymm]
    (h : H.IsExtremallyMatched s t) (h₀ : H.IsSimple) {F : Set (Sym2 V × ℕ)} {k : ℕ}
    (h₁ : H.incidentEdges c t ⊆ F) (h₂ : w ∈ s) (h₃ : H.earliestNeighborFn w = some u)
    (h₄ : y ∈ t) (h₅ : (Subgraph.fromEdgeSet G F).ReachableBefore x u k)
    (h₆ : ∃ a ∈ H.arcTime u c, k ≤ a)
    (h₇ : ∃ a ∈ H.arcTime c u, ∃ b ∈ H.arcTime c y, a ≤ b) :
    (Subgraph.fromEdgeSet G F).Reachable x y := by
  obtain ⟨a, ha, hka⟩ := h₆
  obtain ⟨a', ha', b, hb, hab⟩ := h₇
  have hut : u ∈ t := h.mem_right_of_earliestNeighborFn_eq_some h₂ h₃
  rw [arcTime_comm h₀ u c] at ha
  obtain rfl : a' = a := Option.some_inj.1 (ha'.symm.trans ha)
  -- `u → c`, an edge at `c`
  have h₉ : (s(u, c), a') ∈ F := by
    rw [Sym2.eq_swap]
    exact h₁ (mem_incidentEdges hut ha)
  have h₈ := h₅.step (Subgraph.adj_fromEdgeSet h₉ <| H.adj_sub (adj_of_arcTime_eq_some ha).symm) hka
  -- `c → y`, an edge at `c`, temporal since `y` comes after `u`
  exact (h₈.step (Subgraph.adj_fromEdgeSet (h₁ (mem_incidentEdges h₄ hb))
    (H.adj_sub (adj_of_arcTime_eq_some hb))) hab).reachable

variable {H : Subgraph G} [Finite H.verts] [H.IsSymm]

/-- Baligács 2026, Observation 9: let `S_cross` be the sources that are `m`-hop-`τ`-cut-crossing
for the source `c`. Some set `E` of at most `m * |S_cross|` edges of `H` makes `E ∪ Star(c)` reach
every target `y` with `τ ≤ λ(c, y)` from every source that is early (`c` reaches its `N_min` by
time `τ`) or crossing. An early source `x` reaches `y` through `x → N_min x → c → y`. A crossing
source uses its own walk to some `N_min w`, then `N_min w → c → y`. -/
theorem exists_reachable_simpleStar (h : H.IsExtremallyMatched s t) (h₀ : H.IsSimple)
    (h₁ : H.IsProper) (c : V) (τ m : ℕ) :
    ∃ E ⊆ H.edgeSet, E.ncard ≤ m * {v ∈ s | H.IsCutCrossing s c τ m v}.ncard ∧
      ∀ x ∈ {v ∈ s | ∃ u ∈ H.earliestNeighborFn v, ∃ k ∈ H.arcTime c u, k ≤ τ} ∪
          {v ∈ s | H.IsCutCrossing s c τ m v},
        ∀ y ∈ {u ∈ t | ∃ k ∈ H.arcTime c u, τ ≤ k},
          (Subgraph.fromEdgeSet G (E ∪ H.simpleStar s t c)).Reachable x y := by
  classical
  -- each crossing source `v` comes with its crossing walk `p v` to some `u = N_min w`
  have hcross : ∀ v, H.IsCutCrossing s c τ m v → ∃ w ∈ s, ∃ u ∈ H.earliestNeighborFn w,
      (∃ k ∈ H.arcTime c u, k ≤ τ) ∧ ∃ n n' : ℕ, ∃ p : H.toTemporalGraph.TemporalWalk v n u n',
        p.length ≤ m ∧ ∃ k ∈ H.arcTime u c, n' ≤ k :=
    fun _ hv ↦ hv.2
  choose w hw u hu hcu n n' p hp hk using hcross
  have hC : {v ∈ s | H.IsCutCrossing s c τ m v}.Finite :=
    (Set.toFinite H.verts).subset
      ((Set.sep_subset _ _).trans (Set.subset_union_left.trans h.subset_verts))
  -- `E` gathers the edges of the crossing walks
  let E : V → Set (Sym2 V × ℕ) := fun v ↦
    if hv : H.IsCutCrossing s c τ m v then {e | e ∈ (p v hv).edges} else ∅
  have hE : ∀ v (hv : H.IsCutCrossing s c τ m v), E v = {e | e ∈ (p v hv).edges} :=
    fun v hv ↦ dite_eq_left hv
  refine ⟨⋃ v ∈ hC.toFinset, E v, ?_, ?_, ?_⟩
  · -- the edges of the walks are edges of `H`
    refine Set.iUnion₂_subset fun v hv ↦ ?_
    rw [hE v (hC.mem_toFinset.1 hv).2]
    exact fun e he ↦ (p v _).edges_subset_edgeSet he
  · -- each crossing walk has at most `m` edges
    calc (⋃ v ∈ hC.toFinset, E v).ncard ≤ ∑ v ∈ hC.toFinset, (E v).ncard :=
          Finset.set_ncard_biUnion_le _ _
      _ ≤ hC.toFinset.card • m := by
          refine Finset.sum_le_card_nsmul _ _ _ fun v hv ↦ ?_
          rw [hE v (hC.mem_toFinset.1 hv).2]
          exact (p v _).ncard_setOf_mem_edges_le.trans (hp v _)
      _ = m * {v ∈ s | H.IsCutCrossing s c τ m v}.ncard := by
          rw [Set.ncard_eq_toFinset_card _ hC, smul_eq_mul, mul_comm]
  · rintro x (⟨hx, u₀, hu₀, k, hk₀, hkτ⟩ | ⟨hx, hxc⟩) y ⟨hy, k', hk', hτk'⟩
    · -- `x → u₀`, an edge of `E_min`, then `u₀ → c → y`
      have hu₁ := Option.mem_def.1 hu₀
      obtain ⟨a, ha⟩ := earliestNeighbor_of_earliestNeighborFn_eq_some hu₁
      have ha' := ha.arcTime_eq_some h₀
      have hkc : H.arcTime u₀ c = some k := by
        rw [arcTime_comm h₀]
        exact Option.mem_def.1 hk₀
      refine h.reachable_of_reachableBefore_earliestNeighborFn h₀
        (fun e he ↦ Or.inr (Or.inr he)) hx hu₁ hy
        ((ReachableWithin.refl x le_rfl).step (Subgraph.adj_fromEdgeSet
          (Or.inr (Or.inl (TemporalGraph.mem_eMin hx hu₁ ha'))) (H.adj_sub ha.1)) (Nat.zero_le _))
        ⟨k, hkc, ?_⟩ ⟨k, hk₀, k', hk', hkτ.trans hτk'⟩
      -- temporal at `u₀`, since `{x, u₀}` is the earliest edge at `u₀`
      exact h.arcTime_le_of_earliestNeighborFn_eq_some h₀ h₁ (Or.inl hx) hu₁ ha' hkc
    · -- a crossing source follows its crossing walk to `u x`, then `u x → c → y`
      have hsub : ∀ e ∈ (p x hxc).edges, e ∈ (⋃ v ∈ hC.toFinset, E v) ∪ H.simpleStar s t c :=
        fun e he ↦ Or.inl (Set.mem_iUnion₂.2 ⟨x, hC.mem_toFinset.2 ⟨hx, hxc⟩, hE x hxc ▸ he⟩)
      obtain ⟨k, hk₀, hkτ⟩ := hcu x hxc
      exact h.reachable_of_reachableBefore_earliestNeighborFn h₀
        (fun e he ↦ Or.inr (Or.inr he)) (hw x hxc) (Option.mem_def.1 (hu x hxc)) hy
        ((p x hxc).reachableBefore_fromEdgeSet hsub) (hk x hxc)
        ⟨k, hk₀, k', hk', hkτ.trans hτk'⟩

end IsExtremallyMatched

end TemporalGraph
