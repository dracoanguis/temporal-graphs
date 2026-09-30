/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic
import TemporalGraph.Subgraph
import TemporalGraph.Bipartite
import TemporalGraph.Connectivity.Subgraph

/-!
# Dismountability

This module formalizes the *dismountability* argument as revisited by Carnevale, Casteigts &
Corsini (SAND 2025, §§2–3), originally due to Casteigts, Peters & Schoeters (CPS, ICALP 2019 /
JCSS), which underlies the `O(n log n)` spanner bound for temporal cliques: a clique
with no dismountable vertex is small enough (via `vzero`) and structured enough (via the
earliest/latest neighbor bijections) to sparsify inductively. See `Dismountability/Operations.lean`
for the operations (`dismount`, `mount`, `twoHopMount`) that carry out the induction.

A subgraph `H` partitions its vertices into `vminus` (vertices that are someone's earliest
neighbor), `vplus` (vertices that are someone's latest neighbor) and `vzero` (neither). `H` is
`Dismountable` when it is a clique with a vertex that is both an earliest and a latest neighbor;
`TwoHopDismountable` weakens this to allow reaching such a vertex within two hops. When `H` is not
two-hop-dismountable, the earliest/latest neighbor relations become bijections between `vminus`
and `vplus` (`earliestNeighborFn`, `latestNeighborFn`), which forces `vzero` to be empty.

## Main definitions

* `TemporalGraph.Subgraph.Dismountable` : SAND 2025, §2, 1-hop dismountability (the hypothesis of
  Theorem 2.1).
* `TemporalGraph.Subgraph.vminus`, `vplus`, `vzero` : SAND 2025, §3.1, `V⁻`/`V⁺`/`V⁰`, the
  partition of `H.verts` defined just before Lemma 3.1.
* `TemporalGraph.Subgraph.TwoHopDismountable` : SAND 2025, §2.1, `{1,2}`-hop dismountability
  (`k`-hop with `k ≤ 2`).
* `TemporalGraph.Subgraph.earliestNeighborFn`, `latestNeighborFn` : the bijections between
  `vminus` and `vplus` obtained when `H` is not two-hop-dismountable.

## Main results

* `TemporalGraph.Subgraph.partition_of_not_dismountable` : SAND 2025, Lemma 3.1, `vminus`, `vplus`,
  `vzero` partition `H.verts`.
* `TemporalGraph.Subgraph.vplus_ne_neighbor_of_not_twoHopDismountable`,
  `vminus_ne_neighbor_of_not_twoHopDismountable` : SAND 2025, Lemma 3.2, distinct vertices of
  `vplus` (resp. `vminus`) have distinct earliest (resp. latest) neighbors.
* `TemporalGraph.Subgraph.earliestNeighborFn_bijective`, `latestNeighborFn_bijective` : the
  bijections between `vminus` and `vplus` (SAND 2025, Corollary 3.3, via Lemma 3.2).
* `TemporalGraph.Subgraph.vzero_empty_of_not_twoHopDismountable` : SAND 2025, Lemma 3.4,
  `vzero = ∅`.

## References

* Carnevale, Casteigts & Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025,
  LIPIcs 330, 6:1–6:18, doi:10.4230/LIPIcs.SAND.2025.6, arXiv:2502.01321.
* Casteigts, Peters & Schoeters, *Temporal Cliques Admit Sparse Spanners*, ICALP 2019 / JCSS
  (original source of the argument).
-/

universe u
variable {V : Type u}

namespace TemporalGraph

namespace Subgraph

variable {G : TemporalGraph V}

section Partition

/-- SAND 2025, §2: 1-hop dismountability (hypothesis of Theorem 2.1). A clique subgraph `H` is
dismountable when some vertex `x` is both the earliest neighbor of some `y` and the latest
neighbor of some `z`. -/
def Dismountable (H : Subgraph G) :=
  H.IsCliqueSubgraph ∧ ∃ (x y z : V), H.EarliestNeighbor y x ∧ H.LatestNeighbor z x

/-- SAND 2025, §3.1: `V⁻`, defined before Lemma 3.1. The set of vertices that are someone's
earliest neighbor. -/
def vminus (H : Subgraph G) : Set V := {x : V | ∃ y : V, H.EarliestNeighbor y x}

/-- `H.vminus` is contained in `H.verts`. -/
@[simp]
lemma vminus_sub_verts {H : Subgraph G} : H.vminus ⊆ H.verts := by
  intro _ ⟨_, ⟨_, h⟩⟩
  exact H.edge_vert' h.left

instance {H : Subgraph G} [h : Finite H.verts] : Finite H.vminus :=
  Set.Finite.subset (H.verts.finite_coe_iff.mp h) vminus_sub_verts

/-- Noncomputable: obtained from the `Finite` instance above via `Classical.choice`. Useful for
stating cardinalities of `vminus` (`Fintype.card`), not for computing with them. -/
noncomputable instance {H : Subgraph G} [Finite H.verts] : Fintype H.vminus :=
  Fintype.ofFinite _

/-- SAND 2025, §3.1: `V⁺`, defined before Lemma 3.1. The set of vertices that are someone's
latest neighbor. -/
def vplus (H : Subgraph G) : Set V := {x : V | ∃ y : V, H.LatestNeighbor y x}

/-- `H.vplus` is contained in `H.verts`. -/
@[simp]
lemma vplus_sub_verts {H : Subgraph G} : H.vplus ⊆ H.verts := by
  intro _ ⟨_, ⟨_, h⟩⟩
  exact H.edge_vert' h.left

instance {H : Subgraph G} [h : Finite H.verts] : Finite H.vplus :=
  Set.Finite.subset (H.verts.finite_coe_iff.mp h) vplus_sub_verts

/-- Noncomputable: obtained from the `Finite` instance above via `Classical.choice`. Useful for
stating cardinalities of `vplus` (`Fintype.card`), not for computing with them. -/
noncomputable instance {H : Subgraph G} [Finite H.verts] : Fintype H.vplus :=
  Fintype.ofFinite _

/-- SAND 2025, §3.1: `V⁰`, defined before Lemma 3.1. The vertices of `H` that are neither in
`vminus` nor `vplus`. -/
def vzero (H : Subgraph G) : Set V := H.verts \ (H.vminus ∪ H.vplus)

/-- `H.vzero` is contained in `H.verts`. -/
@[simp]
lemma vzero_sub_verts {H : Subgraph G} : H.vzero ⊆ H.verts := by
  intro _ ⟨h, _⟩
  exact h

instance {H : Subgraph G} [h : Finite H.verts] : Finite H.vzero :=
  Set.Finite.subset (H.verts.finite_coe_iff.mp h) vzero_sub_verts

/-- Noncomputable: obtained from the `Finite` instance above via `Classical.choice`. Useful for
stating cardinalities of `vzero` (`Fintype.card`), not for computing with them. -/
noncomputable instance {H : Subgraph G} [Finite H.verts] : Fintype H.vzero :=
  Fintype.ofFinite _

/-- A vertex of `H.vzero` lies in neither `H.vminus` nor `H.vplus`. -/
lemma vzero_mem {H : Subgraph G} : ∀ x : V, x ∈ H.vzero → x ∉ H.vminus ∧ x ∉ H.vplus := by
  intro _ hx
  simp [vzero] at hx
  simp [hx]

instance {H : Subgraph G} : Coe (Set V) (Set H.verts) where
  coe A := (Subtype.val ⁻¹' A)

/-- `vminus`, `vplus` and `vzero` cover `H.verts`. -/
lemma vunion_eq_univ {H : Subgraph G} : H.vminus ∪ H.vplus ∪ H.vzero = H.verts := by
  simp [vzero]

/-- `H.vplus` and `H.vminus` intersect iff `H` is a dismountable clique. -/
lemma nonempty_vplus_inter_vminus_iff_dismountable (H : Subgraph G) :
    H.IsCliqueSubgraph ∧ (H.vplus ∩ H.vminus).Nonempty ↔ H.Dismountable := by
  rw [Dismountable, Set.nonempty_def, vminus, vplus]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, exists_and_left, exists_and_right, And.comm]

/-- SAND 2025, Lemma 3.1: for a clique that is not dismountable, `vminus`, `vplus` and `vzero`
partition `H.verts` into a disjoint cover. -/
lemma partition_of_not_dismountable {H : Subgraph G} (h : H.IsCliqueSubgraph ∧ ¬H.Dismountable) :
    ∀ x ∈ H.verts, ∃! s ∈ ({H.vminus, H.vplus, H.vzero} : Set (Set V)), x ∈ s := by
  have ⟨hClique, hnDis⟩ := h
  conv at hnDis => rhs ; rw [←nonempty_vplus_inter_vminus_iff_dismountable]
  push Not at hnDis
  have hnDis := hnDis hClique
  simp only [Set.ext_iff, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false] at hnDis
  have hnDis' := hnDis
  simp only [And.comm] at hnDis'
  simp only [not_and] at hnDis hnDis'
  have hvm : H.vminus ⊆ (Set.univ : Set V) := Set.subset_univ H.vminus
  have hvz : H.vzero ⊆ (Set.univ : Set V) := Set.subset_univ H.vzero
  have hvp : H.vplus ⊆ (Set.univ : Set V) := Set.subset_univ H.vplus
  intro u
  by_cases hempty : (Set.univ : Set V) = ∅
  · intro _
    use H.vminus
    rw [hempty] at hvm hvp hvz
    have hvmeqe := Set.eq_empty_of_subset_empty hvm
    have hvpeqe := Set.eq_empty_of_subset_empty hvp
    have hvzeqe := Set.eq_empty_of_subset_empty hvz
    rw [←hempty] at hvmeqe hvpeqe hvzeqe
    simp ; constructor
    <;> simp [hvpeqe, hvzeqe, hvmeqe]
  · by_cases huin : u ∈ H.vzero
    · intro _
      use H.vzero ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_and,
      and_imp, forall_eq_or_imp, forall_eq, implies_true, and_true]
      constructor ; assumption' ; constructor
      <;> intro huin' <;> absurd huin' <;> simp [(vzero_mem u huin)]
    · by_cases huin' : u ∈ H.vminus
      · intro _
        use H.vminus ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, true_and,
        and_imp, forall_eq_or_imp, implies_true, forall_eq]
        constructor ; assumption' ; constructor
        <;> intro huin'' <;> absurd huin''
        · exact hnDis' u huin'
        · trivial
      · by_cases huin'' : u ∈ H.vplus
        · intro _
          use H.vplus ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
          true_and, and_imp, forall_eq_or_imp, implies_true, forall_eq]
          split_ands
          assumption'
          all_goals intro _ ; contradiction
        · intro hin
          push Not at hempty ; rw [Set.nonempty_def] at hempty
          have hunin : u ∉ H.verts := by rw [←H.vunion_eq_univ] ; simp [huin, huin', huin'']
          contradiction

end Partition

section TwoHop

/-- SAND 2025, §2.1: `{1,2}`-hop dismountability (`k`-hop, `k ≤ 2`). A clique subgraph `H` is
two-hop dismountable when some vertex `x` is reached within at most two hops both from an
earliest edge and from a latest edge. -/
def TwoHopDismountable (H : Subgraph G) :=
  H.IsCliqueSubgraph
  ∧
  (∃ x : V,
    ((∃ y : V, H.EarliestNeighbor y x)
      ∨ (∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.EarliestEdge y z n ∧ H.Adj z x m ∧ m ≤ n))
    ∧
    ((∃ y : V, H.LatestNeighbor y x)
      ∨ (∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.LatestEdge y z n ∧ H.Adj z x m ∧ n ≤ m)))

/-- A dismountable clique is `{1,2}`-hop dismountable. -/
@[simp]
lemma twoHopDismountable_of_dismountable {H : Subgraph G} (h : H.Dismountable) :
    H.TwoHopDismountable := by
  constructor
  · exact h.left
  · rcases h.right with ⟨u, α, β, hen, hln⟩
    use u
    constructor <;> apply Or.inl
    · exists α
    · exists β

/-- A clique that is not `{1,2}`-hop dismountable is not dismountable. -/
@[simp]
lemma not_dismountable_of_not_twoHopDismountable {H : Subgraph G}
    (h : H.IsCliqueSubgraph ∧ ¬H.TwoHopDismountable) :
    ¬H.Dismountable := by
  contrapose h
  simp only [h, twoHopDismountable_of_dismountable, not_true_eq_false, and_false, not_false_eq_true]

/-- SAND 2025, Lemma 3.2: distinct vertices of `vplus` have distinct earliest neighbors. -/
lemma vplus_ne_neighbor_of_not_twoHopDismountable {H : Subgraph G} [H.IsSymm]
    (x y : H.vplus) (h₀ : ¬H.TwoHopDismountable) (h₁ : H.IsCliqueSubgraph) (h₂ : x ≠ y) :
    ∀ z z' : V, H.EarliestNeighbor x z ∧ H.EarliestNeighbor y z' → z ≠ z' := by
  simp only [EarliestNeighbor, ne_eq, and_imp, forall_exists_index]
  intro z z' n hee m hee' hzz'
  have ⟨x, hx⟩ := x
  have ⟨y, hy⟩ := y
  absurd h₀
  constructor ; assumption'
  by_cases ht : m ≤ n
  · use y
    constructor
    · apply Or.inr
      use x, z, n, m
      constructor
      · simpa using h₂
      · constructor
        · assumption
        · constructor
          · rw [←hzz'] at hee' ; exact H.adj_symm hee'.left
          · assumption
    · apply Or.inl ; assumption
  · use x
    constructor
    · apply Or.inr
      use y, z', m, n
      constructor
      · simpa using h₂.symm
      · constructor
        · assumption
        · constructor
          · rw [hzz'] at hee ; exact H.adj_symm hee.left
          · push Not at ht ; apply ht.le
    · apply Or.inl ; assumption

/-- SAND 2025, Lemma 3.2: distinct vertices of `vminus` have distinct latest neighbors. -/
lemma vminus_ne_neighbor_of_not_twoHopDismountable {H : Subgraph G} [H.IsSymm]
    (x y : H.vminus) (h₀ : ¬H.TwoHopDismountable) (h₁ : H.IsCliqueSubgraph) (h₂ : x ≠ y) :
    ∀ z z' : V, H.LatestNeighbor x z ∧ H.LatestNeighbor y z' → z ≠ z' := by
  simp only [LatestNeighbor, ne_eq, and_imp, forall_exists_index]
  intro z z' n hle m hle' hzz'
  have ⟨x, hx⟩ := x
  have ⟨y, hy⟩ := y
  absurd h₀
  constructor ; assumption'
  by_cases ht : n ≤ m
  · use y
    constructor
    · apply Or.inl ; assumption
    · apply Or.inr
      use x, z, n, m
      constructor
      · simpa using h₂
      · constructor
        · assumption
        · constructor
          · rw [←hzz'] at hle' ; exact H.adj_symm hle'.left
          · assumption
  · use x
    constructor
    · apply Or.inl ; assumption
    · apply Or.inr
      use y, z', m, n
      constructor
      · simpa using h₂.symm
      · constructor
        · assumption
        · constructor
          · rw [hzz'] at hle ; exact H.adj_symm hle.left
          · push Not at ht ; apply ht.le

end TwoHop

section NeighborFunctions

/-- Every vertex of a finite, nontrivial, simple clique subgraph has an earliest incident
edge. -/
lemma earliestEdge_exists_of_finite_nontrivial_simple_clique {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) :
    ∀ (x : H.verts), ∃ (y : V) (n : ℕ), H.EarliestEdge x y n := by
  intro x
  have his₀ : (H.incidenceSet x).Nonempty := nonempty_incidenceSet_of_nontrivial_clique h₁ x
  have his₁ : (H.incidenceSet x).Finite := finite_incidenceSet_of_finite_simple h₀ x
  exact earliestEdge_exists_of_nonempty_finite_incidenceSet his₀ his₁

/-- Every vertex of a finite, nontrivial, simple clique subgraph has a latest incident
edge. -/
lemma latestEdge_exists_of_finite_nontrivial_simple_clique {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) :
    ∀ (x : H.verts), ∃ (y : V) (n : ℕ), H.LatestEdge x y n := by
  intro x
  have his₀ : (H.incidenceSet x).Nonempty := nonempty_incidenceSet_of_nontrivial_clique h₁ x
  have his₁ : (H.incidenceSet x).Finite := finite_incidenceSet_of_finite_simple h₀ x
  exact latestEdge_exists_of_nonempty_finite_incidenceSet his₀ his₁

/-- Every vertex of a finite, nontrivial, simple, proper clique subgraph has a unique earliest
incident edge. -/
lemma earliestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    ∀ (x : H.verts), ∃! q : V × ℕ, H.EarliestEdge x q.1 q.2 := by
  intro x
  have ⟨y, n, h⟩ := earliestEdge_exists_of_finite_nontrivial_simple_clique h₀ h₁ x
  use ⟨y, n⟩
  constructor
  · simp [h]
  · intro ⟨z, m⟩ h'
    simp only [Prod.mk.injEq]
    have hle := h.right _ _ h'.left
    have hle' := h'.right _ _ h.left
    have heq := hle.ge_iff_eq.mp hle'
    have hadj := h'.left
    rw [heq.symm] at hadj
    have heq' := h₂ x y z n ⟨h.left, hadj⟩
    exact ⟨heq'.symm, heq.symm⟩

/-- Every vertex of a finite, nontrivial, simple, proper clique subgraph has a unique latest
incident edge. -/
lemma latestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    ∀ (x : H.verts), ∃! q : V × ℕ, H.LatestEdge x q.1 q.2 := by
  intro x
  have ⟨y, n, h⟩ := latestEdge_exists_of_finite_nontrivial_simple_clique h₀ h₁ x
  use ⟨y, n⟩
  constructor
  · simp [h]
  · intro ⟨z, m⟩ h'
    simp only [Prod.mk.injEq]
    have hle := h.right _ _ h'.left
    have hle' := h'.right _ _ h.left
    have heq := hle.ge_iff_eq.mp hle'
    have hadj := h'.left
    rw [heq] at hadj
    have heq' := h₂ x y z n ⟨h.left, hadj⟩
    exact ⟨heq'.symm, heq⟩

/-- Every vertex of a finite, nontrivial, simple, proper clique subgraph has a unique earliest
neighbor. -/
lemma existsUnique_earliestNeighbor {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    ∀ x : H.verts, ∃! y : H.vminus, H.EarliestNeighbor x y := by
  intro x
  obtain ⟨⟨y, n⟩, hee, hunique⟩ :=
    earliestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique
      h₀ h₁ h₂ x
  use ⟨y, ⟨_, ⟨n, hee⟩⟩⟩
  refine ⟨⟨n, hee⟩, ?_⟩
  intro z ⟨m, hee'⟩
  obtain heq := hunique ⟨z, m⟩ hee'
  rw [Prod.eq_iff_fst_eq_snd_eq] at heq
  ext
  exact heq.left

/-- The earliest-neighbor function from `vplus` to `vminus`, sending `x` to its unique earliest
neighbor (see `existsUnique_earliestNeighbor`). -/
noncomputable def earliestNeighborFn {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    H.vplus → H.vminus :=
  fun x => Classical.choose
    (existsUnique_earliestNeighbor h₀ h₁ h₂ ⟨x.val, vplus_sub_verts x.prop⟩).exists

/-- Characterizes `earliestNeighborFn` in terms of `EarliestNeighbor`. -/
lemma earliestNeighborFn_eq {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] {x : H.vplus} {y : H.vminus}
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    (earliestNeighborFn h₀ h₁ h₂) x = y ↔ H.EarliestNeighbor x y := by
  unfold earliestNeighborFn
  constructor
  <;> intro h
  · subst h
    grind only [usr Exists.choose_spec]
  · have ⟨y', hee, hunique⟩:= existsUnique_earliestNeighbor h₀ h₁ h₂ ⟨x, vplus_sub_verts x.prop⟩
    grind only [usr Exists.choose_spec]

/-- `earliestNeighborFn` is injective when `H` is a finite, nontrivial, simple, proper clique
that is not `{1,2}`-hop dismountable (used to build the `vminus`/`vplus` bijection). -/
lemma earliestNeighborFn_injective {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    Function.Injective (earliestNeighborFn h₀ h₁ h₂) := by
  intro x y
  by_contra! ⟨hfeq, hneq⟩
  let (eq := hz) z := earliestNeighborFn h₀ h₁ h₂ x
  let (eq := hz') z'  := earliestNeighborFn h₀ h₁ h₂ y
  rw [←hz, ←hz'] at hfeq
  have hz₁ := hz
  have hz'₁ := hz'
  rw [earliestNeighborFn_eq, ←hz] at hz₁
  rw [earliestNeighborFn_eq, ←hz'] at hz'₁
  have := vplus_ne_neighbor_of_not_twoHopDismountable x y h₃ h₁ hneq z z' ⟨hz₁, hz'₁⟩
  absurd this
  simp only [hfeq]

/-- `vplus` has at most as many elements as `vminus`, via injectivity of `earliestNeighborFn`. -/
lemma vplus_card_le_vminus_card {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    Fintype.card H.vplus ≤ Fintype.card H.vminus :=
  Fintype.card_le_of_injective (earliestNeighborFn h₀ h₁ h₂)
    (earliestNeighborFn_injective h₀ h₁ h₂ h₃)

/-- Every vertex of a finite, nontrivial, simple, proper clique subgraph has a unique latest
neighbor. -/
lemma existsUnique_latestNeighbor {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    ∀ x : H.verts, ∃! y : H.vplus, H.LatestNeighbor x y := by
  intro x
  obtain ⟨⟨y, n⟩, hle, hunique⟩ :=
    latestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique
      h₀ h₁ h₂ x
  use ⟨y, ⟨_, ⟨n, hle⟩⟩⟩
  refine ⟨⟨n, hle⟩, ?_⟩
  intro z ⟨m, hle'⟩
  obtain heq := hunique ⟨z, m⟩ hle'
  rw [Prod.eq_iff_fst_eq_snd_eq] at heq
  ext
  exact heq.left

/-- The latest-neighbor function from `vminus` to `vplus`, sending `x` to its unique latest
neighbor (see `existsUnique_latestNeighbor`). -/
noncomputable def latestNeighborFn {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    H.vminus → H.vplus :=
  fun x => Classical.choose
    (existsUnique_latestNeighbor h₀ h₁ h₂ ⟨x.val, vminus_sub_verts x.prop⟩).exists

/-- Characterizes `latestNeighborFn` in terms of `LatestNeighbor`. -/
lemma latestNeighborFn_eq {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] {x : H.vminus} {y : H.vplus}
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    (latestNeighborFn h₀ h₁ h₂) x = y ↔ H.LatestNeighbor x y := by
  unfold latestNeighborFn
  constructor
  <;> intro h
  · subst h
    grind only [usr Exists.choose_spec]
  · have ⟨y', hee, hunique⟩:= existsUnique_latestNeighbor h₀ h₁ h₂ ⟨x, vminus_sub_verts x.prop⟩
    grind only [usr Exists.choose_spec]

/-- `latestNeighborFn` is injective when `H` is a finite, nontrivial, simple, proper clique
that is not `{1,2}`-hop dismountable (used to build the `vminus`/`vplus` bijection). -/
lemma latestNeighborFn_injective {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    Function.Injective (latestNeighborFn h₀ h₁ h₂) := by
  intro x y
  by_contra! ⟨hfeq, hneq⟩
  let (eq := hz) z := latestNeighborFn h₀ h₁ h₂ x
  let (eq := hz') z'  := latestNeighborFn h₀ h₁ h₂ y
  rw [←hz, ←hz'] at hfeq
  have hz₁ := hz
  have hz'₁ := hz'
  rw [latestNeighborFn_eq, ←hz] at hz₁
  rw [latestNeighborFn_eq, ←hz'] at hz'₁
  have := vminus_ne_neighbor_of_not_twoHopDismountable x y h₃ h₁ hneq z z' ⟨hz₁, hz'₁⟩
  absurd this
  simp only [hfeq]

/-- `vminus` has at most as many elements as `vplus`, via injectivity of `latestNeighborFn`. -/
lemma vminus_card_le_vplus_card {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    Fintype.card H.vminus ≤ Fintype.card H.vplus :=
  Fintype.card_le_of_injective (latestNeighborFn h₀ h₁ h₂)
    (latestNeighborFn_injective h₀ h₁ h₂ h₃)

/-- SAND 2025, Corollary 3.3 (3): `vminus` and `vplus` have the same cardinality. -/
lemma vminus_card_eq_vplus_card {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    Fintype.card H.vminus = Fintype.card H.vplus :=
  Nat.le_antisymm (vminus_card_le_vplus_card h₀ h₁ h₂ h₃)
    (vplus_card_le_vminus_card h₀ h₁ h₂ h₃)

/-- SAND 2025, Corollary 3.3 (via Lemma 3.2): `earliestNeighborFn` gives a bijection between
`vplus` and `vminus`. -/
lemma earliestNeighborFn_bijective {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    Function.Bijective (earliestNeighborFn h₀ h₁ h₂) := by
  apply Iff.mpr <| Fintype.bijective_iff_injective_and_card (earliestNeighborFn h₀ h₁ h₂)
  constructor
  · exact earliestNeighborFn_injective h₀ h₁ h₂ h₃
  · exact (vminus_card_eq_vplus_card h₀ h₁ h₂ h₃).symm

/-- SAND 2025, Corollary 3.3 (via Lemma 3.2): `latestNeighborFn` gives a bijection between
`vminus` and `vplus`. -/
lemma latestNeighborFn_bijective {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    Function.Bijective (latestNeighborFn h₀ h₁ h₂) := by
  apply Iff.mpr <| Fintype.bijective_iff_injective_and_card (latestNeighborFn h₀ h₁ h₂)
  constructor
  · exact latestNeighborFn_injective h₀ h₁ h₂ h₃
  · exact vminus_card_eq_vplus_card h₀ h₁ h₂ h₃

/-- SAND 2025, Corollary 3.3 (1): `{e⁻(v) : v ∈ V⁺}` is a perfect matching, i.e. every vertex of
`vminus` has a unique earliest edge from a vertex of `vplus`. -/
lemma existsUnique_vplus_earliestEdge {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    ∀ x : H.vminus, ∃! q : H.vplus × ℕ, H.EarliestEdge q.1 x q.2 := by
  intro x
  have hen_bij := earliestNeighborFn_bijective h₀ h₁ h₂ h₃ |>.existsUnique
  conv at hen_bij =>
    rhs ; rhs
    simp only [earliestNeighborFn_eq]
  have ⟨y, ⟨n, hee⟩, hunique⟩ := hen_bij x
  use ⟨y, n⟩
  refine ⟨hee, ?_⟩
  intro q' hee'
  have heq := hunique q'.1 ⟨q'.2, hee'⟩
  have hadj := hee'.left
  rw [heq] at hadj
  have heq' := h₀ y x n q'.2 ⟨hee.left, hadj⟩
  exact Prod.eq_iff_fst_eq_snd_eq.mpr ⟨heq, heq'.symm⟩

/-- SAND 2025, Corollary 3.3 (2): `{e⁺(v) : v ∈ V⁻}` is a perfect matching, i.e. every vertex of
`vplus` has a unique latest edge from a vertex of `vminus`. -/
lemma existsUnique_vminus_latestEdge {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    ∀ x : H.vplus, ∃! q : H.vminus × ℕ, H.LatestEdge q.1 x q.2 := by
  intro x
  have hln_bij := latestNeighborFn_bijective h₀ h₁ h₂ h₃ |>.existsUnique
  conv at hln_bij =>
    rhs ; rhs
    simp only [latestNeighborFn_eq]
  have ⟨y, ⟨n, hle⟩, hunique⟩ := hln_bij x
  use ⟨y, n⟩
  refine ⟨hle, ?_⟩
  intro q' hle'
  have heq := hunique q'.1 ⟨q'.2, hle'⟩
  have hadj := hle'.left
  rw [heq] at hadj
  have heq' := h₀ y x n q'.2 ⟨hle.left, hadj⟩
  exact Prod.eq_iff_fst_eq_snd_eq.mpr ⟨heq, heq'.symm⟩

end NeighborFunctions

section VzeroEmpty

/-- SAND 2025, Lemma 3.4: in a clique that is not `{1,2}`-hop dismountable, `V⁰ = ∅`. -/
lemma vzero_empty_of_not_twoHopDismountable {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    H.vzero = ∅ := by
  by_contra! ⟨x, hx⟩
  have ⟨y, n, hee⟩ :=
    earliestEdge_exists_of_finite_nontrivial_simple_clique h₀ h₁ ⟨x, vzero_sub_verts hx⟩
  have hyin : y ∈ H.vminus := ⟨x, ⟨n, hee⟩⟩
  have ⟨z, m, hle⟩ :=
    latestEdge_exists_of_finite_nontrivial_simple_clique h₀ h₁ ⟨x, vzero_sub_verts hx⟩
  have hzin : z ∈ H.vplus := ⟨x, ⟨m, hle⟩⟩
  -- Here call SAND 2025 Corollary 3.3 to define y' ∈ H.vplus with y it's earliest neighbor
  -- symm for z' ∈ H.vminus with z it's latest neighbor
  have ⟨⟨⟨y', hy'in⟩, n'⟩, ⟨hee', _⟩⟩ :=
    existsUnique_vplus_earliestEdge h₀ h₁ h₂ h₃ ⟨y, hyin⟩
  have ⟨⟨⟨z', hz'in⟩, m'⟩, ⟨hle', _⟩⟩ :=
    existsUnique_vminus_latestEdge h₀ h₁ h₂ h₃ ⟨z, hzin⟩
  by_cases hlt : n' ≤ n
  <;> absurd h₃
  · constructor
    · trivial
    · use y'
      have ⟨⟨⟨y'', _⟩, _⟩, ⟨hle'', _⟩⟩ :=
        existsUnique_vminus_latestEdge h₀ h₁ h₂ h₃ ⟨y', hy'in⟩
      refine ⟨?_, Or.inl ⟨y'', ⟨_, hle''⟩⟩⟩
      apply Or.inr
      use x, y, n, n'
      refine ⟨?_, hee, H.adj_symm hee'.left, hlt⟩
      intro heq
      absurd hy'in
      rw [heq] at hx
      exact (vzero_mem y' hx).right
  · constructor
    · trivial
    · by_cases hlt' : m ≤ m'
      · -- Same as above with z and hee instead of y and hle
        use z'
        have ⟨⟨⟨z'', _⟩, _⟩, ⟨hee'', _⟩⟩ :=
          existsUnique_vplus_earliestEdge h₀ h₁ h₂ h₃ ⟨z', hz'in⟩
        refine ⟨Or.inl ⟨z'', ⟨_, hee''⟩⟩, ?_⟩
        apply Or.inr
        use x, z, m, m'
        refine ⟨?_, hle, H.adj_symm hle'.left, hlt'⟩
        intro heq
        absurd hz'in
        rw [heq] at hx
        exact (vzero_mem z' hx).left
      · use x
        constructor
        <;> apply Or.inr
        · use y', y, n' , n
          refine ⟨?_, hee', H.adj_symm hee.left, Nat.le_of_not_le hlt⟩
          intro heq
          absurd hy'in
          rw [←heq] at hx
          exact (vzero_mem y' hx).right
        · use z', z, m', m
          refine ⟨?_, hle', H.adj_symm hle.left, Nat.le_of_not_le hlt'⟩
          intro heq
          absurd hz'in
          rw [←heq] at hx
          exact (vzero_mem z' hx).left

end VzeroEmpty

section Reciprocity

/-- SAND 2025, Lemma 3.5 (Reciprocity), first statement: if `v u` occurs at time `n` as `v`'s
earliest edge, every edge from `u` to a vertex of `vplus` occurs no earlier than `n`. -/
lemma earliestEdge_reciprocity {H : Subgraph G} [H.IsSymm] {u v : V} {n : ℕ}
    (h₀ : H.IsCliqueSubgraph) (h₁ : ¬H.TwoHopDismountable) (h : H.EarliestEdge v u n) :
    ∀ w ∈ H.vplus, ∀ j, H.Adj u w j → n ≤ j := by
  intro w hw j hj
  by_contra! hlt
  -- `w` reaches `v` in two hops, through `u` then `e⁻(v)`; and `w ∈ V⁺`
  refine h₁ ⟨h₀, w, Or.inr ⟨v, u, n, j, ?_, h, hj, hlt.le⟩, Or.inl hw⟩
  rintro rfl
  exact absurd (h.2 u j hj.symm) (by omega)

/-- SAND 2025, Lemma 3.5 (Reciprocity), second statement: if `u v` occurs at time `n` as `u`'s
latest edge, every edge from `v` to a vertex of `vminus` occurs no later than `n`. -/
lemma latestEdge_reciprocity {H : Subgraph G} [H.IsSymm] {u v : V} {n : ℕ}
    (h₀ : H.IsCliqueSubgraph) (h₁ : ¬H.TwoHopDismountable) (h : H.LatestEdge u v n) :
    ∀ w ∈ H.vminus, ∀ j, H.Adj v w j → j ≤ n := by
  intro w hw j hj
  by_contra! hlt
  -- `w ∈ V⁻`; and `u` reaches `w` in two hops, through `e⁺(u)` then `v`
  refine h₁ ⟨h₀, w, Or.inl hw, Or.inr ⟨u, v, n, j, ?_, h, hj, hlt.le⟩⟩
  rintro rfl
  exact absurd (h.2 v j hj.symm) (by omega)

end Reciprocity

section biclique

/-- SAND 2025, Corollary 4.1: when `H` is not `{1,2}`-hop dismountable, the bipartite subgraph
between `vminus` and `vplus` is a bi-clique on those two sets. -/
lemma biclique_of_not_twoHopDismountable {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsCliqueSubgraph) (h₁ : ¬H.TwoHopDismountable) :
    (H.between H.vminus H.vplus).IsBicliqueWith H.vminus H.vplus := by
  apply IsClique.between_isBicliqueWith h₀ vminus_sub_verts vplus_sub_verts
  apply Set.disjoint_iff_inter_eq_empty.mpr
  have hnDis := not_dismountable_of_not_twoHopDismountable ⟨h₀, h₁⟩
  conv at hnDis => rhs ; rw [←nonempty_vplus_inter_vminus_iff_dismountable]
  push Not at hnDis
  conv => lhs ; apply Set.inter_comm
  apply hnDis h₀

/-- SAND 2025, remark after Corollary 4.1: the bi-clique between `vminus` and `vplus` is always
temporally connected. -/
lemma between_TC_of_not_twoHopDismountable {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    (H.between H.vminus H.vplus).TemporallyConnectedSubgraph := by
  set K := H.between H.vminus H.vplus
  have hbc : K.IsBicliqueWith H.vminus H.vplus := biclique_of_not_twoHopDismountable h₁ h₃
  have hmem : ∀ v ∈ H.verts, v ∈ H.vminus ∨ v ∈ H.vplus := by
    intro v hv
    by_contra hc
    push Not at hc
    have hz : v ∈ H.vzero := ⟨hv, by simp [hc.1, hc.2]⟩
    rw [vzero_empty_of_not_twoHopDismountable h₀ h₁ h₂ h₃] at hz
    exact hz
  -- an edge across the bi-clique, in both directions
  have hdirect : ∀ v w, v ∈ H.vminus → w ∈ H.vplus →
      K.toTemporalGraph.Reachable v w ∧ K.toTemporalGraph.Reachable w v := by
    intro v w hv hw
    obtain ⟨n, hn⟩ := hbc.adj_of_mem hv hw
    exact ⟨reachable_of_nonempty_NonemptyTemporalWalk ⟨n, n, ⟨.Single hn⟩⟩,
      reachable_of_nonempty_NonemptyTemporalWalk ⟨n, n, ⟨.Single hn.symm⟩⟩⟩
  intro x hx y hy
  rcases hmem x hx with hxm | hxp <;> rcases hmem y hy with hym | hyp
  · -- both in `V⁻`: through the vertex of `V⁺` whose earliest edge goes to `x`
    obtain ⟨⟨⟨p, hp⟩, n⟩, hpe, -⟩ := existsUnique_vplus_earliestEdge h₀ h₁ h₂ h₃ ⟨x, hxm⟩
    have hKe : K.toTemporalGraph.EarliestEdge p x n :=
      ⟨⟨hpe.1, Or.inr ⟨hp, hxm⟩⟩, fun z j hz ↦ hpe.2 z j hz.1⟩
    exact TemporalGraph.reachable_of_earliestEdge hKe y (hdirect y p hym hp).2
  · exact (hdirect x y hxm hyp).1
  · exact (hdirect y x hym hxp).2
  · -- both in `V⁺`: through the vertex of `V⁻` whose latest edge goes to `y`
    obtain ⟨⟨⟨a, ha⟩, n⟩, hal, -⟩ := existsUnique_vminus_latestEdge h₀ h₁ h₂ h₃ ⟨y, hyp⟩
    have hKl : K.toTemporalGraph.LatestEdge a y n :=
      ⟨⟨hal.1, Or.inl ⟨ha, hyp⟩⟩, fun z j hz ↦ hal.2 z j hz.1⟩
    exact TemporalGraph.reachable_of_latestEdge hKl x (hdirect a x ha hxp).2


end biclique

end Subgraph

end TemporalGraph
