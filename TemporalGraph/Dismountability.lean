/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic
import TemporalGraph.SubTemporalGraph

universe u
variable {V : Type u}

namespace SimpleTemporalGraph

-- Theorem 2.1
def Dismountable (G : SimpleTemporalGraph V) :=
  ∃ (x y z : V), G.EarliestNeighbor y x ∧ G.LatestNeighbor z x

namespace SubTemporalGraph

variable {G : SimpleTemporalGraph V}

-- Theorem 2.1
def Dismountable (H : SubTemporalGraph G) :=
  H.IsClique ∧ ∃ (x y z : V), H.EarliestNeighbor y x ∧ H.LatestNeighbor z x

def Dismountable' (H : SubTemporalGraph G) (x y z : V) (n m : ℕ) :=
  H.IsClique ∧ H.EarliestEdge y x n ∧ H.LatestEdge z x m

abbrev Dismount (H : SubTemporalGraph G) (x : V) := H.deleteVerts {x}

-- def 3.1
def Vminus (H : SubTemporalGraph G) : Set V := {x : V | ∃ y : V, H.EarliestNeighbor y x}

@[simp]
lemma vminus_sub_verts {H : SubTemporalGraph G} : H.Vminus ⊆ H.Verts := by
  intro _ ⟨_, ⟨_, h⟩⟩
  exact h.left.snd_mem

-- def 3.1
def Vplus (H : SubTemporalGraph G) : Set V := {x : V | ∃ y : V, H.LatestNeighbor y x}

@[simp]
lemma vplus_sub_verts {H : SubTemporalGraph G} : H.Vplus ⊆ H.Verts := by
  intro _ ⟨_, ⟨_, h⟩⟩
  exact h.left.snd_mem

-- def 3.1
def Vzero (H : SubTemporalGraph G) : Set V := H.Verts \ (H.Vminus ∪ H.Vplus)

-- False, definition is too vague
-- @[simp]
-- lemma vzero_sub_verts {H : SubTemporalGraph G} : H.Vzero ⊆ H.Verts := by
--   intro x ⟨⟩

lemma vzero_mem {H : SubTemporalGraph G} : ∀ x : V, x ∈ H.Vzero → x ∉ H.Vminus ∧ x ∉ H.Vplus := by
  intro _ hx
  simp [Vzero] at hx
  simp [hx]

lemma vunion_eq_univ {H : SubTemporalGraph G} : H.Vminus ∪ H.Vplus ∪ H.Vzero = H.Verts := by
  simp [Vzero]

lemma nonempty_vplus_inter_vmimus_iff_Dismountable (H : SubTemporalGraph G) :
    H.IsClique ∧ (H.Vplus ∩ H.Vminus).Nonempty ↔ H.Dismountable := by
  rw [Dismountable, Set.nonempty_def, Vminus, Vplus]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, exists_and_left, exists_and_right, And.comm]

-- lemma 3.1
lemma partition_of_not_dismountable {H : SubTemporalGraph G} (h : H.IsClique ∧ ¬H.Dismountable) :
    ∀ x ∈ H.Verts, ∃! s ∈ ({H.Vminus, H.Vplus, H.Vzero} : Set (Set V)), x ∈ s := by
  have ⟨hClique, hnDis⟩ := h
  conv at hnDis => rhs ; rw [←nonempty_vplus_inter_vmimus_iff_Dismountable]
  push_neg at hnDis
  have hnDis := hnDis hClique
  simp only [Set.ext_iff, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false] at hnDis
  have hnDis' := hnDis
  simp only [And.comm] at hnDis'
  simp only [not_and] at hnDis hnDis'
  have hvm : H.Vminus ⊆ (Set.univ : Set V) := Set.subset_univ H.Vminus
  have hvz : H.Vzero ⊆ (Set.univ : Set V) := Set.subset_univ H.Vzero
  have hvp : H.Vplus ⊆ (Set.univ : Set V) := Set.subset_univ H.Vplus
  intro u
  rw [ExistsUnique]
  by_cases hempty : (Set.univ : Set V) = ∅
  · intro _
    use H.Vminus
    rw [hempty] at hvm hvp hvz
    have hvmeqe := Set.eq_empty_of_subset_empty hvm
    have hvpeqe := Set.eq_empty_of_subset_empty hvp
    have hvzeqe := Set.eq_empty_of_subset_empty hvz
    rw [←hempty] at hvmeqe hvpeqe hvzeqe
    simp ; constructor
    <;> simp   [hvpeqe, hvzeqe, hvmeqe]
  · by_cases huin : u ∈ H.Vzero
    · intro _
      use H.Vzero ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_and,
      and_imp, forall_eq_or_imp, forall_eq, implies_true, and_true]
      constructor ; assumption' ; constructor
      <;> intro huin' <;> absurd huin' <;> simp [(vzero_mem u huin)]
    · by_cases huin' : u ∈ H.Vminus
      · intro _
        use H.Vminus ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, true_and,
        and_imp, forall_eq_or_imp, implies_true, forall_eq]
        constructor ; assumption' ; constructor
        <;> intro huin'' <;> absurd huin''
        · exact hnDis' u huin'
        · exact huin
      · by_cases huin'' : u ∈ H.Vplus
        · intro _
          use H.Vplus ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
          true_and, and_imp, forall_eq_or_imp, implies_true, forall_eq]
          constructor ; assumption' ; constructor
          <;> intro huin''' <;> contradiction
        · intro hin
          push_neg at hempty ; rw [Set.nonempty_def] at hempty
          have hunin : u ∉ H.Verts := by rw [←H.vunion_eq_univ] ; simp [huin, huin', huin'']
          absurd hunin
          exact hin

def Dismountable2 (H : SubTemporalGraph G) :=
  H.IsClique
  ∧
  (∃ x : V,
    ((∃ y : V, H.EarliestNeighbor y x)
      ∨ (∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.EarliestEdge y z n ∧ H.Adj z x m ∧ m ≤ n))
    ∧
    ((∃ y : V, H.LatestNeighbor y x)
      ∨ (∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.LatestEdge y z n ∧ H.Adj z x m ∧ n ≤ m)))

lemma dismountable2_of_dismountable {H : SubTemporalGraph G} (h : H.Dismountable) :
    H.Dismountable2 := by
  constructor
  · exact h.left
  · rcases h.right with ⟨u, α, β, hen, hln⟩
    use u
    constructor <;> apply Or.inl
    · exists α
    · exists β

lemma not_dismountable_of_not_dismountable2 {H : SubTemporalGraph G}
    (h : H.IsClique ∧ ¬H.Dismountable2) :
    ¬H.Dismountable := by
  contrapose h ; simp at * ; simp [h, dismountable2_of_dismountable]

-- lemma 3.2
lemma vplus_ne_neighbor_of_not_dismountable2 {H : SubTemporalGraph G} (x y : H.Vplus)
    (h : ¬H.Dismountable2) (h₁ : H.IsClique) (h₂ : x ≠ y) :
    ∀ z z', H.EarliestNeighbor x z ∧ H.EarliestNeighbor y z' → z ≠ z' := by
  simp only [EarliestNeighbor, ne_eq, and_imp, forall_exists_index]
  intro z z' n hee m hee' hzz'
  have ⟨x, hx⟩ := x
  have ⟨y, hy⟩ := y
  rw [Vplus] at hx hy
  absurd h
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
          · rw [←hzz'] at hee' ; exact hee'.left.symm
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
          · rw [hzz'] at hee ; exact hee.left.symm
          · push_neg at ht ; apply ht.le
    · apply Or.inl ; assumption

-- lemma 3.2
lemma vminus_ne_neighbor_of_not_dismountable2 {H : SubTemporalGraph G} (x y : H.Vminus)
    (h : ¬H.Dismountable2) (h₁ : H.IsClique) (h₂ : x ≠ y) :
    ∀ z z', H.LatestNeighbor x z ∧ H.LatestNeighbor y z' → z ≠ z' := by
  simp only [LatestNeighbor, ne_eq, and_imp, forall_exists_index]
  intro z z' n hle m hle' hzz'
  have ⟨x, hx⟩ := x
  have ⟨y, hy⟩ := y
  rw [Vminus] at hx hy
  absurd h
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
          · rw [←hzz'] at hle' ; exact hle'.left.symm
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
          · rw [hzz'] at hle ; exact hle.left.symm
          · push_neg at ht ; apply ht.le

-- -- Corollary 3.3
-- lemma notDismountable2_imp_PerfectMatching {G' : SubTemporalGraph G}
-- : ¬G'.Dismountable2 →

lemma earliestEdge_exists_of_finite_nontrivial_simple_clique {H : SubTemporalGraph G}
    [h₀ : Finite H.Verts]
    [h₁ : Nontrivial H.Verts]
    (h₂ : H.IsSimple)
    (h₃ : H.IsClique) :
    ∀ (x : H.Verts), ∃ (y : V) (n : ℕ), H.EarliestEdge x y n := by
  intro x
  have his₀ : (H.IncidenceSet x).Nonempty := nonempty_incidenceSet_of_nontrivial_clique h₃ x
  have his₁ : (H.IncidenceSet x).Finite := finite_incidenceSet_of_finite_simple h₂ x
  exact earliestEdge_exists_of_nonempty_finite_incidenceSet his₀ his₁

lemma latestEdge_exists_of_finite_nontrivial_simple_clique {H : SubTemporalGraph G}
    [h₀ : Finite H.Verts]
    [h₁ : Nontrivial H.Verts]
    (h₂ : H.IsSimple)
    (h₃ : H.IsClique) :
    ∀ (x : H.Verts), ∃ (y : V) (n : ℕ), H.LatestEdge x y n := by
  intro x
  have his₀ : (H.IncidenceSet x).Nonempty := nonempty_incidenceSet_of_nontrivial_clique h₃ x
  have his₁ : (H.IncidenceSet x).Finite := finite_incidenceSet_of_finite_simple h₂ x
  exact latestEdge_exists_of_nonempty_finite_incidenceSet his₀ his₁

lemma earliestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique {H : SubTemporalGraph G}
    [h₀ : Finite H.Verts]
    [h₁ : Nontrivial H.Verts]
    (h₂ : H.IsSimple)
    (h₃ : H.IsClique)
    (h₄ : H.IsProper) :
    ∀ (x : H.Verts), ∃! q : V × ℕ, H.EarliestEdge x q.1 q.2 := by
  intro x
  have ⟨y, n, h⟩ := earliestEdge_exists_of_finite_nontrivial_simple_clique h₂ h₃ x
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
    have heq' := h₄ ⟨h.left, hadj⟩
    exact ⟨heq'.symm, heq.symm⟩

lemma latestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique {H : SubTemporalGraph G}
    [Finite H.Verts]
    [Nontrivial H.Verts]
    (h₁ : H.IsSimple)
    (h₂ : H.IsClique)
    (h₃ : H.IsProper) :
    ∀ (x : H.Verts), ∃! q : V × ℕ, H.LatestEdge x q.1 q.2 := by
  intro x
  have ⟨y, n, h⟩ := latestEdge_exists_of_finite_nontrivial_simple_clique h₁ h₂ x
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
    have heq' := h₃ ⟨h.left, hadj⟩
    exact ⟨heq'.symm, heq⟩

-- Till +23 is useless because not used after but true
-- def EarliestEdgeSet (H : SubTemporalGraph G) : Set (V × V × ℕ) :=
--   {(x, y, n) : V × V × ℕ | H.EarliestEdge x y n}

-- def EarliestEdgeGraph (H : SubTemporalGraph G) : SubTemporalGraph G  :=
--   G.fromEdgeSet H.EarliestEdgeSet

-- lemma earliestEdgeGraph_sub {H : SubTemporalGraph G} : H.EarliestEdgeGraph ≤ H := by
--   constructor
--   · rw [Set.subset_def]
--     intro x h
--     have ⟨a, ⟨⟨hadj, _⟩, hax⟩⟩ := h
--     apply Or.elim hax
--     <;> intro heq <;> rw [heq.symm] at hadj
--     · exact hadj.fst_mem
--     · exact hadj.snd_mem
--   · intro x y n ⟨a, ⟨⟨hadjH, _⟩, heq, heqn, _⟩⟩
--     rw [heqn]
--     apply Or.elim heq
--     <;> intro heq
--     <;> rw [heq.left, heq.right]
--     ·  exact hadjH
--     ·  exact hadjH.symm

-- Impossible to define currently
-- lemma matching_a_nommer {H : SubTemporalGraph G}
--     [h₀ : Finite H.Verts]
--     [h₁ : Nontrivial H.Verts]
--     (h₂ : H.IsSimple)
--     (h₃ : H.IsClique)
--     (h₄ : H.IsProper)
--     (h₅ : ¬H.Dismountable2) :
--   H.

-- Wrongly defined, untrue
-- lemma earliestEdgeGraph_perfectStrictMatching_of_not_dismountable2 {H : SubTemporalGraph G}
--     [h₀ : Finite H.Verts]
--     [h₁ : Nontrivial H.Verts]
--     (h₂ : H.IsSimple)
--     (h₃ : H.IsClique)
--     (h₄ : H.IsProper)
--     (h₅ : ¬H.Dismountable2) :
--     H.EarliestEdgeGraph.IsPerfectStrictMatchingOf H := by
--   have hspanning : H.EarliestEdgeGraph.Verts = H.Verts := by
--     apply Set.eq_of_subset_of_subset earliestEdgeGraph_sub.left
--     intro x h
--     dsimp [EarliestEdgeGraph, fromEdgeSet, EarliestEdgeSet]
--     have ⟨y, n, hee⟩ := earliestEdge_exists_of_finite_nontrivial_simple_clique h₂ h₃ ⟨x, h⟩
--     use ⟨x, y, n⟩
--     simp only [hee, true_or, and_self]
--   constructor
--   · unfold IsStrictMatching
--     intro x hin
--     -- EE needs to be unique?
--     dsimp [EarliestEdgeGraph, fromEdgeSet, EarliestEdgeSet]
--     rw [hspanning] at hin
--     have ⟨q, hee, heqq⟩ := earliestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique h₂ h₃ h₄ ⟨x, hin⟩
--     simp_all
--     use q
--     dsimp
--     constructor
--     · skip
--       use x, q.1
--       exact ⟨hee, Or.inl ⟨rfl, rfl⟩, hee.left.adj_sub⟩
--     · skip
--       intro q' ⟨y, y', ⟨hee', heqq', _⟩⟩
--       apply Or.elim heqq'
--       <;> intro heq
--       <;> rw [←heq.left, ←heq.right] at hee'
--       · exact heqq _ _ hee'
--       · skip
--         apply heqq
--         constructor
--         · exact hee'.left.symm
--         · intro z m h
--           haveI := hee.right _ _ h
--           haveI := hee.right _ _ hee'.left.symm


--   · trivial

-- lemma 3.4 -- Impossible because of vzero not defined correctly
lemma vzero_empty_of_not_dismountable2 {H : SubTemporalGraph G}
    [Finite H.Verts]
    [Nontrivial H.Verts]
    (h₁ : H.IsSimple)
    (h₂ : H.IsClique)
    (h₃ : H.IsProper)
    (h₄ : ¬H.Dismountable2) :
    H.Vzero = ∅ := by
  by_contra! ⟨x, hx⟩
  have hee := earliestEdge_exists_of_finite_nontrivial_simple_clique h₁ h₂ ⟨x, hx.⟩


end SubTemporalGraph

end SimpleTemporalGraph
