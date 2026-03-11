import TemporalGraph.PROOF.Basic

universe u
variable {V : Type u}

namespace SimpleTemporalGraph

-- Theorem 2.1
def Dismountable (G : SimpleTemporalGraph V)
:= ∃ (x y z : V), G.EarliestNeigbhor y x ∧ G.LatestNeighbor z x

namespace SubTempGraph

variable {G : SimpleTemporalGraph V}

-- Theorem 2.1
def Dismountable (H : SubTempGraph G)
:= H.IsClique ∧ ∃ (x y z : V), H.EarliestNeighbor y x ∧ H.LatestNeighbor z x

def Dismountable' (H : SubTempGraph G) (x y z : V) (n m : ℕ)
:= H.IsClique ∧ H.EarliestEdge y x n ∧ H.LatestEdge z x m

abbrev Dismount (H : SubTempGraph G) (x : V) := H.deleteVerts {x}

-- def 3.1
def Vminus (H : SubTempGraph G) : Set V
:= {x : V | ∃ y : V, H.EarliestNeighbor y x}

-- def 3.1
def Vplus (H : SubTempGraph G) : Set V
:= {x : V | ∃ y : V, H.LatestNeighbor y x}

-- def 3.1
def Vzero (H : SubTempGraph G) : Set V
:= (H.Vminusᶜ ∩ H.Vplusᶜ)

lemma vzero_univ_diff {H : SubTempGraph G} : H.Vzero = Set.univ \ (H.Vminus ∪ H.Vplus)
:= by simp [Vzero, Set.diff_eq]

lemma vzero_mem {H : SubTempGraph G} : ∀ x : V, x ∈ H.Vzero → x ∉ H.Vminus ∧ x ∉ H.Vplus
:= by
  intro _ hx
  simp [Vzero, Set.compl_def] at hx
  simp [hx]

lemma vunion_eq_univ {H : SubTempGraph G} : H.Vminus ∪ H.Vplus ∪ H.Vzero = Set.univ
:= by simp [vzero_univ_diff]

lemma nonempty_vplus_inter_vmimus_iff_Dismountable (H : SubTempGraph G)
: H.IsClique ∧ (H.Vplus ∩ H.Vminus).Nonempty ↔ H.Dismountable
:= by
  rw [Dismountable, Set.nonempty_def, Vminus, Vplus]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, exists_and_left, exists_and_right, And.comm]

-- lemma 3.1
lemma partition_of_not_dismountable {H : SubTempGraph G}
(h : H.IsClique ∧ ¬H.Dismountable)
: ∀ x : V, ∃! s ∈ ({H.Vminus, H.Vplus, H.Vzero} : Set (Set V)), x ∈ s
:= by
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
  · use H.Vminus
    rw [hempty] at hvm hvp hvz
    have hvmeqe := Set.eq_empty_of_subset_empty hvm
    have hvpeqe := Set.eq_empty_of_subset_empty hvp
    have hvzeqe := Set.eq_empty_of_subset_empty hvz
    rw [←hempty] at hvmeqe hvpeqe hvzeqe
    simp ; constructor
    <;> simp   [hvpeqe, hvzeqe, hvmeqe]
  · by_cases huin : u ∈ H.Vzero
    · use H.Vzero ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_and,
      and_imp, forall_eq_or_imp, forall_eq, implies_true, and_true]
      constructor ; assumption' ; constructor
      <;> intro huin' <;> absurd huin' <;> simp [(vzero_mem u huin)]
    · by_cases huin' : u ∈ H.Vminus
      · use H.Vminus ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, true_and,
        and_imp, forall_eq_or_imp, implies_true, forall_eq]
        constructor ; assumption' ; constructor
        <;> intro huin'' <;> absurd huin''
        · exact hnDis' u huin'
        · exact huin
      · by_cases huin'' : u ∈ H.Vplus
        · use H.Vplus ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
          true_and, and_imp, forall_eq_or_imp, implies_true, forall_eq]
          constructor ; assumption' ; constructor
          <;> intro huin''' <;> contradiction
        · push_neg at hempty ; rw [Set.nonempty_def] at hempty
          have hunin : u ∉ Set.univ := by rw [←H.vunion_eq_univ] ; simp [huin, huin', huin'']
          absurd hunin
          apply Set.mem_univ

def Dismountable2 (H : SubTempGraph G)
:= H.IsClique ∧ ( ∃ x : V,
    ((∃ y : V, H.EarliestNeighbor y x)
      ∨ (∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.EarliestEdge y z n ∧ H.Adj z x m ∧ m ≤ n))
  ∧ ((∃ y : V, H.LatestNeighbor y x)
      ∨ (∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.LatestEdge y z n ∧ H.Adj z x m ∧ n ≤ m))
  )

lemma dismountable2_of_dismountable {H : SubTempGraph G}
(h : H.Dismountable) : H.Dismountable2
:= by
  constructor
  · exact h.left
  · rcases h.right with ⟨u, α, β, hen, hln⟩
    use u
    constructor <;> apply Or.inl
    · exists α
    · exists β

lemma not_dismountable_of_not_dismountable2 {H : SubTempGraph G}
(h : H.IsClique ∧ ¬H.Dismountable2)
: ¬H.Dismountable
:= by contrapose h ; simp at * ; simp [h, dismountable2_of_dismountable]

-- lemma 3.2
lemma vplus_ne_neighbor_of_not_dismountable2 {H : SubTempGraph G}
(x y : H.Vplus) (h : ¬H.Dismountable2) (h₁ : H.IsClique) (h₂ : x ≠ y)
: ∀ z z', H.EarliestNeighbor x z ∧ H.EarliestNeighbor y z' → z ≠ z'
:= by
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
lemma notDismountable2_neDiff_imp_neigbhorDiff' {H : SubTempGraph G}
(x y : H.Vminus) (h : ¬H.Dismountable2) (h₁ : H.IsClique) (h₂ : x ≠ y)
: ∀ z z', H.LatestNeighbor x z ∧ H.LatestNeighbor y z' → z ≠ z'
:= by
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
-- lemma notDismountable2_imp_PerfectMatching {G' : SubTempGraph G}
-- : ¬G'.Dismountable2 →

-- lemma 3.3
lemma vzero_empty_of_not_dismountable2 {H : SubTempGraph G}
(h : H.IsClique)
: ¬H.Dismountable2 → H.Vzero = ∅
:= by sorry
  -- by_contra h'
  -- push_neg at h'
  -- have ⟨hnDis, hVne⟩ := h'




end SubTempGraph

end SimpleTemporalGraph
