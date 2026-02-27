import TemporalGraph.PROOF.Basic

universe u
variable {V : Type u}

namespace SimpleTemporalGraph

-- Theorem 2.1
def Dismountable (G : SimpleTemporalGraph V)
:= ∃ u α β, G.EarliestNeigbhor α u ∧ G.LatestNeighbor β u

namespace SubTempGraph

variable {G : SimpleTemporalGraph V}

-- Theorem 2.1
def Dismountable (G' : SubTempGraph G)
:= G'.IsClique ∧ ∃ u α β, G'.EarliestNeigbhor α u ∧ G'.LatestNeighbor β u

def Dismountable' (G' : SubTempGraph G) (u α β : V) (te tl : ℕ)
:= G'.IsClique ∧ G'.EarliestEdge α u te ∧ G'.LatestEdge β u tl

abbrev Dismount (G' : SubTempGraph G) (u : V) := G'.deleteVerts {u}

-- def 3.1
def Vminus (G' : SubTempGraph G) : Set V
:= {u | ∃ α, G'.EarliestNeigbhor α u}

-- def 3.1
def Vplus (G' : SubTempGraph G) : Set V
:= {u | ∃ β, G'.LatestNeighbor β u}

-- def 3.1
def Vzero (G' : SubTempGraph G) : Set V
:= (G'.Vminusᶜ ∩ G'.Vplusᶜ)

lemma vzero_eq {G' : SubTempGraph G} : G'.Vzero = Set.univ \ (G'.Vminus ∪ G'.Vplus)
:= by simp [Vzero, Set.diff_eq]

lemma vzero_mem {G' : SubTempGraph G} : ∀ x, x ∈ G'.Vzero → x ∉ G'.Vminus ∧ x ∉ G'.Vplus
:= by
  intro _ hx
  simp [Vzero, Set.compl_def] at hx
  simp [hx]

lemma vunion_eq_univ {G' : SubTempGraph G} : G'.Vminus ∪ G'.Vplus ∪ G'.Vzero = Set.univ
:= by simp [vzero_eq]

lemma notEmpty_Vplus_inter_Vmimus_iff_Dismountable
(G' : SubTempGraph G)
: G'.IsClique ∧ (G'.Vplus ∩ G'.Vminus).Nonempty ↔ G'.Dismountable
:= by
  rw [Dismountable, Set.nonempty_def, Vminus, Vplus]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, exists_and_left, exists_and_right, And.comm]

-- lemma 3.1
lemma notDismountable_imp_partition
{G' : SubTempGraph G} (h : G'.IsClique ∧ ¬G'.Dismountable)
: ∀ u, ∃! b ∈ ({G'.Vminus, G'.Vplus, G'.Vzero} : Set (Set V)), u ∈ b
:= by
  have ⟨hClique, hnDis⟩ := h
  conv at hnDis => rhs ; rw [←notEmpty_Vplus_inter_Vmimus_iff_Dismountable]
  push_neg at hnDis
  have hnDis := hnDis hClique
  simp only [Set.ext_iff, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false] at hnDis
  have hnDis' := hnDis
  simp only [And.comm] at hnDis'
  simp only [not_and] at hnDis hnDis'
  have hvm : G'.Vminus ⊆ (Set.univ : Set V) := Set.subset_univ G'.Vminus
  have hvz : G'.Vzero ⊆ (Set.univ : Set V) := Set.subset_univ G'.Vzero
  have hvp : G'.Vplus ⊆ (Set.univ : Set V) := Set.subset_univ G'.Vplus
  intro u
  rw [ExistsUnique]
  by_cases hempty : (Set.univ : Set V) = ∅
  · use G'.Vminus
    rw [hempty] at hvm hvp hvz
    have hvmeqe := Set.eq_empty_of_subset_empty hvm
    have hvpeqe := Set.eq_empty_of_subset_empty hvp
    have hvzeqe := Set.eq_empty_of_subset_empty hvz
    rw [←hempty] at hvmeqe hvpeqe hvzeqe
    simp ; constructor
    <;> simp   [hvpeqe, hvzeqe, hvmeqe]
  · by_cases huin : u ∈ G'.Vzero
    · use G'.Vzero ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_and,
      and_imp, forall_eq_or_imp, forall_eq, implies_true, and_true]
      constructor ; assumption' ; constructor
      <;> intro huin' <;> absurd huin' <;> simp [(vzero_mem u huin)]
    · by_cases huin' : u ∈ G'.Vminus
      · use G'.Vminus ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, true_and,
        and_imp, forall_eq_or_imp, implies_true, forall_eq]
        constructor ; assumption' ; constructor
        <;> intro huin'' <;> absurd huin''
        · exact hnDis' u huin'
        · exact huin
      · by_cases huin'' : u ∈ G'.Vplus
        · use G'.Vplus ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
          true_and, and_imp, forall_eq_or_imp, implies_true, forall_eq]
          constructor ; assumption' ; constructor
          <;> intro huin''' <;> contradiction
        · push_neg at hempty ; rw [Set.nonempty_def] at hempty
          have hunin : u ∉ Set.univ := by rw [←G'.vunion_eq_univ] ; simp [huin, huin', huin'']
          absurd hunin
          apply Set.mem_univ

def Dismountable2 (G' : SubTempGraph G)
:= G'.IsClique ∧ ( ∃ u,
    ((∃ α, G'.EarliestNeigbhor α u)
      ∨ (∃ α α' t t', G'.EarliestEdge α α' t ∧ G'.Adj α' u t' ∧ t' ≤ t))
  ∧ ((∃ β, G'.LatestNeighbor β u)
      ∨ (∃ β β' t t', G'.LatestEdge β β' t ∧ G'.Adj β' u t' ∧ t ≤ t'))
  )

lemma Dismountable_imp_Dismountable2 {G' : SubTempGraph G}
(h : G'.Dismountable) : G'.Dismountable2
:= by
  constructor
  · exact h.left
  · rcases h.right with ⟨u, α, β, hen, hln⟩
    use u
    constructor <;> apply Or.inl
    · exists α
    · exists β

lemma notDismountable2_imp_notDismountable
{G' : SubTempGraph G} (h : G'.IsClique ∧ ¬G'.Dismountable2)
: ¬ G'.Dismountable
:= by contrapose h ; simp at * ; simp [h, Dismountable_imp_Dismountable2]

-- lemma 3.2
lemma notDismountable2_neDiff_imp_neigbhorDiff
{G' : SubTempGraph G}
(u v : G'.Vplus) (h : ¬G'.Dismountable2) (h' : G'.IsClique)
: ∀ w w', G'.EarliestNeigbhor u w ∧ G'.EarliestNeigbhor v w' → w ≠ w'
:= by
  simp only [EarliestNeigbhor, ne_eq, and_imp, forall_exists_index]
  intro w w' t hee t' hee' hww'
  have ⟨u, hu⟩ := u
  have ⟨v, hv⟩ := v
  rw [Vplus] at hu hv
  absurd h
  constructor ; assumption'
  by_cases ht : t' ≤ t
  · use v
    constructor
    · apply Or.inr
      use u, w, t, t'
      constructor ; assumption' ; constructor
      · rw [←hww'] at hee' ; exact hee'.left.symm
      · assumption
    · apply Or.inl ; assumption
  · use u
    constructor
    · apply Or.inr
      use v, w', t', t
      constructor ; assumption' ; constructor
      · rw [hww'] at hee ; exact hee.left.symm
      · push_neg at ht ; apply ht.le
    · apply Or.inl ; assumption

example {G' : SubTempGraph G} (u : G'.Vplus) (h' : ¬G'.Dismountable2) (h'' : G'.IsClique)
(h''' : ∃ w, G'.EarliestNeigbhor u w)
: ¬G'.IsClique
:= by
  have ⟨w, hee⟩ := h'''
  have h := notDismountable2_neDiff_imp_neigbhorDiff u u h' h'' w w ⟨hee, hee⟩
  contradiction

-- lemma 3.2
-- lemma notDismountable2_neDiff_imp_neigbhorDiff'
-- {G' : SubTempGraph G}
-- (u v : G'.Vminus) (h' : ¬G'.Dismountable2) (h'' : G'.IsClique)
-- : ∀ w w', G'.LatestNeighbor u w ∧ G'.LatestNeighbor v w' → w ≠ w'
-- := by
--   simp [LatestNeighbor]
--   intro w w' t hle t' hle' hww'
--   have ⟨u, hu⟩ := u
--   have ⟨v, hv⟩ := v
--   rw [Vminus] at *

--   absurd h'
--   constructor ; assumption'

--   by_cases ht : t ≤ t'
--   · use v
--     constructor
--     · apply Or.inl ; assumption
--     · apply Or.inr
--       use u, w, t, t'
--       constructor ; assumption' ; constructor
--       · rw [←hww'] at hle' ; exact hle'.left.symm
--       · assumption
--   · use u
--     constructor
--     · apply Or.inl ; assumption
--     · apply Or.inr
--       use v, w', t', t
--       constructor ; assumption' ; constructor
--       · rw [hww'] at hle ; exact hle.left.symm
--       · push_neg at ht ; apply ht.le

-- -- Corollary 3.3
-- lemma notDismountable2_imp_PerfectMatching {G' : SubTempGraph G}
-- : ¬G'.Dismountable2 →

-- -- lemma 3.3
-- lemma notDismountable2_imp_VzeroEmpty {G' : SubTempGraph G}
-- (h : G'.IsClique)
-- : ¬G'.Dismountable2 → G'.Vzero = ∅
-- := by
--   intro hnDis



end SubTempGraph

end SimpleTemporalGraph
