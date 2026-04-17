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

instance {H : SubTemporalGraph G} [h : Finite H.Verts] : Finite H.Vminus :=
  Set.Finite.subset (H.Verts.finite_coe_iff.mp h) vminus_sub_verts

-- def 3.1
def Vplus (H : SubTemporalGraph G) : Set V := {x : V | ∃ y : V, H.LatestNeighbor y x}

@[simp]
lemma vplus_sub_verts {H : SubTemporalGraph G} : H.Vplus ⊆ H.Verts := by
  intro _ ⟨_, ⟨_, h⟩⟩
  exact h.left.snd_mem

instance {H : SubTemporalGraph G} [h : Finite H.Verts] : Finite H.Vplus :=
  Set.Finite.subset (H.Verts.finite_coe_iff.mp h) vplus_sub_verts

-- def 3.1
def Vzero (H : SubTemporalGraph G) : Set V := H.Verts \ (H.Vminus ∪ H.Vplus)

@[simp]
lemma vzero_sub_verts {H : SubTemporalGraph G} : H.Vzero ⊆ H.Verts := by
  intro _ ⟨h, _⟩
  exact h

instance {H : SubTemporalGraph G} [h : Finite H.Verts] : Finite H.Vzero :=
  Set.Finite.subset (H.Verts.finite_coe_iff.mp h) vzero_sub_verts

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

@[simp]
lemma dismountable2_of_dismountable {H : SubTemporalGraph G} (h : H.Dismountable) :
    H.Dismountable2 := by
  constructor
  · exact h.left
  · rcases h.right with ⟨u, α, β, hen, hln⟩
    use u
    constructor <;> apply Or.inl
    · exists α
    · exists β

@[simp]
lemma not_dismountable_of_not_dismountable2 {H : SubTemporalGraph G}
    (h : H.IsClique ∧ ¬H.Dismountable2) :
    ¬H.Dismountable := by
  contrapose h ; simp at * ; simp [h, dismountable2_of_dismountable]

-- lemma 3.2
lemma vplus_ne_neighbor_of_not_dismountable2 {H : SubTemporalGraph G} (x y : H.Vplus)
    (h₀ : ¬H.Dismountable2) (h₁ : H.IsClique) (h₂ : x ≠ y) :
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
    (h₀ : ¬H.Dismountable2) (h₁ : H.IsClique) (h₂ : x ≠ y) :
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

lemma autre_truc_a_nommer {H : SubTemporalGraph G}
    [Finite H.Verts]
    [Nontrivial H.Verts]
    (h₀ : H.IsSimple)
    (h₁ : H.IsClique)
    (h₂ : H.IsProper) :
    ∀ x : H.Verts, ∃! y : H.Vminus, H.EarliestNeighbor x y := by
  intro ⟨x, hx⟩
  obtain ⟨⟨y, n⟩, hee, hunique⟩ :=
    earliestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique
      h₀ h₁ h₂ ⟨x, hx⟩
  use ⟨y, ⟨_, ⟨n, hee⟩⟩⟩
  refine ⟨⟨n, hee⟩, ?_⟩
  intro ⟨z, hz⟩ ⟨m, hee'⟩
  obtain heq := hunique ⟨z, m⟩ hee'
  rw [Prod.mk.injEq] at heq
  simp only [heq.left]

lemma autre_truc_a_nommer' {H : SubTemporalGraph G}
    [Finite H.Verts]
    [Nontrivial H.Verts]
    (h₀ : H.IsSimple)
    (h₁ : H.IsClique)
    (h₂ : H.IsProper) :
    ∀ x : H.Verts, ∃! y : H.Vplus, H.LatestNeighbor x y := by
  intro ⟨x, hx⟩
  obtain ⟨⟨y, n⟩, hle, hunique⟩ :=
    latestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique
      h₀ h₁ h₂ ⟨x, hx⟩
  use ⟨y, ⟨_, ⟨n, hle⟩⟩⟩
  refine ⟨⟨n, hle⟩, ?_⟩
  intro ⟨z, hz⟩ ⟨m, hle'⟩
  obtain heq := hunique ⟨z, m⟩ hle'
  rw [Prod.mk.injEq] at heq
  simp only [heq.left]

lemma autre_truc_truc_a_nommer {H : SubTemporalGraph G}
    [Finite H.Verts]
    [Nontrivial H.Verts]
    (h₀ : H.IsSimple)
    (h₁ : H.IsClique)
    (h₂ : H.IsProper)
    (h₃ : ¬H.Dismountable2) :
    (Fintype.ofFinite H.Vplus).card ≤ (Fintype.ofFinite H.Vminus).card := by
  -- Utiliser vplus_ne_neighbor_of_not_dismountable2 pour montrer que
  -- la fonction "earliest neighbor" est injective sur Vplus

  -- Définir f : Vplus → Vminus par x ↦ earliest neighbor de x
  -- Puisque Vplus ⊆ Verts, et chaque x ∈ Verts a un unique earliest neighbor par autre_truc_a_nommer
  have f : H.Vplus → H.Vminus := fun ⟨x, hx_mem⟩ => by
    -- x ∈ Vplus ⇒ x ∈ Verts (par vplus_sub_verts)
    have hx_verts : x ∈ H.Verts := vplus_sub_verts hx_mem
    -- Par autre_truc_a_nommer, il existe unique z ∈ Vminus tel que EarliestNeighbor x z
    obtain ⟨⟨z, hz⟩, _, _⟩ := autre_truc_a_nommer h₀ h₁ h₂ ⟨x, hx_verts⟩
    exact ⟨z, hz⟩

  -- Montrer que f est injective en utilisant vplus_ne_neighbor_of_not_dismountable2
  have f_inj : Function.Injective f := by
    intro ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ heq
    simp only [Subtype.mk.injEq] at heq ⊢
    by_cases h : x₁ = x₂
    · exact h
    · -- Si x₁ ≠ x₂ et f(x₁) = f(x₂), on obtient une contradiction via vplus_ne_neighbor_of_not_dismountable2
      exfalso
      have hx₁_verts : x₁ ∈ H.Verts := vplus_sub_verts hx₁
      have hx₂_verts : x₂ ∈ H.Verts := vplus_sub_verts hx₂
      -- Par autre_truc_a_nommer, on récupère les earliest neighbors
      obtain ⟨⟨z₁, hz₁⟩, ⟨n₁, hen₁⟩, hunique₁⟩ := autre_truc_a_nommer h₀ h₁ h₂ ⟨x₁, hx₁_verts⟩
      obtain ⟨⟨z₂, hz₂⟩, ⟨n₂, hen₂⟩, hunique₂⟩ := autre_truc_a_nommer h₀ h₁ h₂ ⟨x₂, hx₂_verts⟩
      -- f(x₁) = ⟨z₁, hz₁⟩ et f(x₂) = ⟨z₂, hz₂⟩
      -- heq dit que ces subtypes dans Vminus sont égaux, donc z₁ = z₂
      have hz_eq : z₁ = z₂ := heq
      -- Mais vplus_ne_neighbor_of_not_dismountable2 dit que z₁ ≠ z₂
      have hz_ne : z₁ ≠ z₂ := vplus_ne_neighbor_of_not_dismountable2
        ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ h₃ h₁ h
        z₁ z₂ ⟨hen₁, hen₂⟩
      exact hz_ne hz_eq

  exact Fintype.card_le_of_embedding ⟨f, f_inj⟩

lemma truc_truc_a_nommer {H : SubTemporalGraph G}
    [Finite H.Verts]
    [Nontrivial H.Verts]
    (h₀ : H.IsSimple)
    (h₁ : H.IsClique)
    (h₂ : H.IsProper)
    (h₃ : ¬H.Dismountable2) :
    ∀ x : H.Vminus, ∃ y : H.Vplus, H.EarliestNeighbor y x := by
  intro ⟨x, hx_prop⟩
  -- hx_prop : ∃ y_src, H.EarliestNeighbor y_src x
  obtain ⟨y_src, ⟨_, hee_edge⟩⟩ := hx_prop
  -- hee_edge : H.EarliestEdge y_src x _
  have hy_verts : y_src ∈ H.Verts := hee_edge.left.fst_mem
  -- Par autre_truc_a_nommer', y_src a un unique latest neighbor w ∈ Vplus
  obtain ⟨⟨w, hw_vplus⟩, _, _⟩ := autre_truc_a_nommer' h₀ h₁ h₂ ⟨y_src, hy_verts⟩
  exact ⟨⟨w, hw_vplus⟩, ⟨_, hee_edge⟩⟩


-- Specialized 3.3 coro, is it true? matching follows of
lemma truc_a_nommer {H : SubTemporalGraph G}
    [Finite H.Verts]
    [Nontrivial H.Verts]
    (h₀ : H.IsSimple)
    (h₁ : H.IsClique)
    (h₂ : H.IsProper)
    (h₃ : ¬H.Dismountable2) :
    ∀ x : H.Vminus, ∃! q : H.Vplus × ℕ, H.EarliestEdge q.1 x q.2 := by
  intro ⟨x, hx_prop⟩
  obtain ⟨y, ⟨n, hee⟩⟩ := hx_prop
  -- y est la source de EarliestNeighbor vers x au temps n
  suffices hy : y ∈ H.Vplus by
    use ⟨⟨y, hy⟩, n⟩
    simp
    refine ⟨hee, ?_⟩
    intro q hee_prime
    obtain ⟨⟨z, hz⟩, m⟩ := q
    by_cases heq : y = z
    · skip
      refine ⟨heq.symm, ?_⟩
      apply h₀
      refine ⟨?_, hee.left.symm⟩
      have hadj := hee_prime.left.symm
      rwa [←heq] at hadj
    · skip
      have hne : x ≠ x :=
        vplus_ne_neighbor_of_not_dismountable2 ⟨y, hy⟩ ⟨z, hz⟩ h₃ h₁ (by simp [heq]) _ _ ⟨⟨n, hee⟩, ⟨m, hee_prime⟩⟩
      absurd hne
      simp
  --Now the true question
  by_contra! hny
  have hy : y ∈ H.Verts := hee.left.fst_mem
  rw [←vunion_eq_univ] at hy
  simp only [Set.mem_union, hny, or_false] at hy
  apply Or.elim hy
  <;> intro hy
  <;> absurd h₃
  · skip
    refine ⟨h₁, ?_⟩
    use x
    refine ⟨Or.inl ⟨_, _, hee⟩, ?_⟩
    have ⟨⟨z, m⟩, hle, _⟩ := latestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique h₀ h₁ h₂ ⟨y, vminus_sub_verts hy⟩
    by_cases heq : z = x
    · skip
      rw [heq] at hle
      exact Or.inl ⟨_, _, hle⟩
    · skip
      apply Or.inr
      use y, z, n, m
      refine ⟨?_, hle, ?_, ?_⟩
  · skip


-- Specialized 3.3 coro
lemma truc_a_nommer' {H : SubTemporalGraph G}
    [Finite H.Verts]
    [Nontrivial H.Verts]
    (h₁ : H.IsSimple)
    (h₂ : H.IsClique)
    (h₃ : H.IsProper)
    (h₄ : ¬H.Dismountable2) :
    ∀ x : H.Vplus, ∃! q : H.Vminus × ℕ, H.LatestEdge q.1 x q.2 := by
  intro x hx
  sorry

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
  have ⟨y, n, hee⟩ := earliestEdge_exists_of_finite_nontrivial_simple_clique h₁ h₂ ⟨x, vzero_sub_verts hx⟩
  have hyin : y ∈ H.Vminus := ⟨x, ⟨n, hee⟩⟩
  have ⟨z, m, hle⟩ := latestEdge_exists_of_finite_nontrivial_simple_clique h₁ h₂ ⟨x, vzero_sub_verts hx⟩
  have hzin : z ∈ H.Vplus := ⟨x, ⟨m, hle⟩⟩
  -- Here call coro 3.3 to define y' ∈ H.Vplus with y it's earliest neighbor
  -- symm for z' ∈ H.Vminus with z it's latest neighbor
  have ⟨⟨⟨y', hy'in⟩, n'⟩, ⟨hee', _⟩⟩ := truc_a_nommer h₁ h₂ h₃ h₄ ⟨y, hyin⟩
  have ⟨⟨⟨z', hz'in⟩, m'⟩, ⟨hle', _⟩⟩ := truc_a_nommer' h₁ h₂ h₃ h₄ ⟨z, hzin⟩
  by_cases hlt : n' ≤ n
  <;> absurd h₄
  · constructor
    · trivial
    · use y'
      have ⟨⟨⟨y'', _⟩, _⟩, ⟨hle'', _⟩⟩ := truc_a_nommer' h₁ h₂ h₃ h₄ ⟨y', hy'in⟩
      refine ⟨?_, Or.inl ⟨y'', ⟨_, hle''⟩⟩⟩
      apply Or.inr
      use x, y, n, n'
      refine ⟨?_, hee, hee'.left.symm, hlt⟩
      intro heq
      absurd hy'in
      rw [heq] at hx
      exact (vzero_mem y' hx).right
  · constructor
    · trivial
    · by_cases hlt' : m ≤ m'
      · -- Same as above with z and hee instead of y and hle
        use z'
        have ⟨⟨⟨z'', _⟩, _⟩, ⟨hee'', _⟩⟩ := truc_a_nommer h₁ h₂ h₃ h₄ ⟨z', hz'in⟩
        refine ⟨Or.inl ⟨z'', ⟨_, hee''⟩⟩, ?_⟩
        apply Or.inr
        use x, z, m, m'
        refine ⟨?_, hle, hle'.left.symm, hlt'⟩
        intro heq
        absurd hz'in
        rw [heq] at hx
        exact (vzero_mem z' hx).left
      · use x
        constructor
        <;> apply Or.inr
        · use y', y, n' , n
          refine ⟨?_, hee', hee.left.symm, Nat.le_of_not_le hlt⟩
          intro heq
          absurd hy'in
          rw [←heq] at hx
          exact (vzero_mem y' hx).right
        · use z', z, m', m
          refine ⟨?_, hle', hle.left.symm, Nat.le_of_not_le hlt'⟩
          intro heq
          absurd hz'in
          rw [←heq] at hx
          exact (vzero_mem z' hx).left

end SubTemporalGraph

end SimpleTemporalGraph
