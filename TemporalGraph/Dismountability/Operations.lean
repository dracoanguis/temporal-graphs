/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic
import TemporalGraph.SubTemporalGraph
import TemporalGraph.Connectivity.SubTemporalGraph

universe u
variable {V : Type u} {G : TemporalGraph V}

namespace TemporalGraph

namespace SubTemporalGraph

section Dismount

abbrev dismount (H : SubTemporalGraph G) (x : V) := H.deleteVerts {x}

lemma dismount_clique (H : SubTemporalGraph G) (x : V) (h₀ : H.IsClique) :
    (H.dismount x).IsClique := by
  unfold IsClique dismount
  intro ⟨y, hy⟩ ⟨z, hz⟩ hne
  simp only [induce_Verts, Set.mem_diff, Set.mem_singleton_iff] at hy hz
  have hy' : y ∈ H.Verts := hy.1
  have hz' : z ∈ H.Verts := hz.1
  have ⟨n, hadj⟩ := h₀ ⟨y, hy'⟩ ⟨z, hz'⟩ (by grind only)
  use n
  simp only [induce_Adj, Set.mem_diff, hy', Set.mem_singleton_iff, true_and, hz', hadj, and_true]
  exact ⟨hy.2, hz.2⟩

@[simp]
lemma dismount_verts {H : SubTemporalGraph G} {x : V} : (H.dismount x).Verts = H.Verts \ {x} := by
  simp only [induce_Verts]

@[simp]
lemma dismount_le {H : SubTemporalGraph G} {x : V} : (H.dismount x) ≤ H := by
  simp only [deleteVerts_le]

end Dismount

section Mount

def mount (H : SubTemporalGraph G) {y z : H.Verts} {n m : ℕ} (x : V) [G.IsSymm]
    (h₀ : G.Adj y x n)
    (h₁ : G.Adj z x m) :
    G.SubTemporalGraph :=
((H.addVerts {x}).addEdgeSymm h₀ (by simp)).addEdgeSymm h₁ (by simp)

@[simp]
lemma mount_verts {H : SubTemporalGraph G} {x : V} {y z : H.Verts} {n m : ℕ} [G.IsSymm]
    (h₀ : G.Adj y x n)
    (h₁ : G.Adj z x m) :
    (mount H x h₀ h₁).Verts = H.Verts ∪ {x} := by
  rw [mount, addEdgeSymm_verts, addEdgeSymm_verts, addVerts_verts]

-- `mount` is a plain `def`, so instance resolution cannot see the `addEdgeSymm`/`addVerts`
-- layers it is built from; this instance unfolds it once and hands the goal back to resolution.
instance mount_isSymm {H : SubTemporalGraph G} {x : V} {y z : H.Verts} {n m : ℕ} [H.IsSymm]
    [G.IsSymm]
    (h₀ : G.Adj y x n)
    (h₁ : G.Adj z x m) :
    (mount H x h₀ h₁).IsSymm := by
  unfold mount
  infer_instance

@[simp]
lemma mem_mount_verts {H : SubTemporalGraph G} {x : V} {y z : H.Verts} {n m : ℕ} [G.IsSymm]
    {h₀ : G.Adj y x n}
    {h₁ : G.Adj z x m}
    (x' : H.Verts) :
    ↑x' ∈ (mount H x h₀ h₁).Verts := by simp [mount_verts]

lemma mount_edge (H : SubTemporalGraph G) {x : V} {y z : H.Verts} {n m : ℕ} [G.IsSymm]
    (h₀ : G.Adj y x n)
    (h₁ : G.Adj z x m) :
    (mount H x h₀ h₁).Adj x y n := by
  simp only [mount, addEdgeSymm, induce_Verts, Set.union_singleton, induce_Adj,
    Set.mem_insert_iff, true_or, true_and, and_true, and_self, or_true]

lemma mount_edge' (H : SubTemporalGraph G) {x : V} {y z : H.Verts} {n m : ℕ} [G.IsSymm]
    (h₀ : G.Adj y x n)
    (h₁ : G.Adj z x m) :
    (mount H x h₀ h₁).Adj z x m := by
  rw [mount]
  apply addEdgeSymm_edge

lemma mount_le {H : SubTemporalGraph G} {x : V} {y z : H.Verts} {n m : ℕ} [G.IsSymm]
    {h₀ : G.Adj y x n}
    {h₁ : G.Adj z x m} :
    H ≤ H.mount x h₀ h₁ := by
  unfold mount
  have h := addVerts_le' H {x}
  have h' := h.trans <| addEdgeSymm_le' (H.addVerts {x}) h₀ (by simp)
  exact le_trans h' addEdgeSymm_le

@[simp]
lemma mount_edgeSet (H : SubTemporalGraph G) {x : V} {y z : H.Verts} {n m : ℕ} [G.IsSymm]
    [G.IsLoopless]
    (h₀ : G.Adj y x n)
    (h₁ : G.Adj z x m) :
    (H.mount x h₀ h₁).EdgeSet = H.EdgeSet ∪ {⟨s(z,x), m⟩, ⟨s(y,x), n⟩} := by
  simp [mount, addEdgeSymm_edgeSet, addVerts_edgeSet]

theorem mount_tc (H : SubTemporalGraph G) {x : V} {y z : H.Verts} {n m : ℕ} [H.IsSymm]
    [G.IsSymm]
    (h₀ : G.Adj y x n)
    (h₁ : G.Adj z x m)
    (h₂ : (mount H x h₀ h₁).EarliestEdge y x n)
    (h₃ : (mount H x h₀ h₁).LatestEdge z x m) :
    H.TemporallyConnected → (mount H x h₀ h₁).TemporallyConnected := by
  have hReach : ∀ x' y', H.Reachable x' y' → (mount H x h₀ h₁).Reachable
    ⟨x', by simp [mount_verts]⟩
    ⟨y', by simp [mount_verts]⟩
    := reachable_of_le_reachable mount_le
  unfold SubTemporalGraph.TemporallyConnected
  intro hTC
  have hy : y.val ∈ (mount H x h₀ h₁).Verts := by simp [mount_verts]
  have hx : x ∈ (mount H x h₀ h₁).Verts := by simp [mount_verts]
  have hz : z.val ∈ (mount H x h₀ h₁).Verts := by simp [mount_verts]
  simp only [Reachable, Subtype.forall, mount_verts, Set.union_singleton, Set.mem_insert_iff]
  intro x' hx' y' hy'
  apply hx'.elim
  · intro heq ; apply hy'.elim
    <;> conv => rhs ; lhs ; lhs ; rw [heq]
    · intro heq'
      conv => rhs ; lhs ; rw [heq']
      simpa using @TemporalGraph.reachable_of_self _ ((mount H x h₀ h₁).coe) ⟨x, _⟩
    · intro hy'₀
      have hy'₁ : y' ∈ (mount H x h₀ h₁).Verts := by simp [hy']
      apply @reachable_of_earliestEdge _ _ (mount H x h₀ h₁) ⟨y, _⟩ ⟨x, _⟩ n inferInstance h₂
        ⟨y', _⟩
      exact hReach ⟨y, _⟩ ⟨y', hy'₀⟩ <| hTC _ _
  · intro hx' ; apply hy'.elim
    · intro heq
      conv => rhs ; lhs ; rw [heq]
      apply @reachable_of_latestEdge _ _ (mount H x h₀ h₁) ⟨z, _⟩ ⟨x, _⟩ m inferInstance h₃
        ⟨x', _⟩
      exact hReach ⟨x', hx'⟩ ⟨z, _⟩ <| hTC _ _
    · intro hy' ; exact hReach ⟨x', hx'⟩ ⟨y', hy'⟩ <| hTC _ _

instance {H : SubTemporalGraph G} [h₀ : Finite H.EdgeSet] {x : V} {y z : H.Verts} {n m : ℕ}
    [G.IsSymm] [G.IsLoopless]
    {h₁ : G.Adj y x n}
    {h₂ : G.Adj z x m} :
    Finite (H.mount x h₁ h₂).EdgeSet := by
  conv =>
    rhs ; rw [H.mount_edgeSet]
  apply Set.Finite.union
  · trivial
  · simp only [Set.finite_insert, Set.finite_singleton]

theorem mount_size {H : SubTemporalGraph G} [Fintype H.EdgeSet] {x : V} {y z : H.Verts} {n m : ℕ}
    [G.IsSymm] [G.IsLoopless]
    {h₀ : G.Adj y x n}
    {h₁ : G.Adj z x m}
    [Fintype (H.mount x h₀ h₁).EdgeSet] :
    Fintype.card (H.mount x h₀ h₁).EdgeSet ≤ Fintype.card H.EdgeSet + 2 := by
  conv => lhs ; simp only [H.mount_edgeSet]
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  have hle₀ : Nat.card ({(s(↑z, x), m), (s(↑y, x), n)} : Set ((Sym2 V) × ℕ)) ≤ 2 := by
    simp only [Nat.card_eq_fintype_card, ←Set.union_singleton]
    have h : 2 = 1 + 1 := by simp only [Nat.reduceAdd]
    have h' : Fintype.card ({(s(↑z, x), m)} : Set (Sym2 V × ℕ)) = 1 := by simp
    have h'' : Fintype.card ({(s(↑y, x), n)} : Set (Sym2 V × ℕ)) = 1 := by simp
    conv => rhs ; rw [h] ; arg 1 ; rw [←h'']
    conv => arg 2 ; arg 2 ; rw [←h']
    simp only [←Nat.card_eq_fintype_card, Set.card_union_le]
  have hle₁ : Nat.card ↑(H.EdgeSet ∪ {(s(↑z, x), m), (s(↑y, x), n)})
      ≤ Nat.card H.EdgeSet + Nat.card ({(s(↑z, x), m), (s(↑y, x), n)} : Set ((Sym2 V) × ℕ)) := by
    simp only [Set.card_union_le]
  lia

theorem dismountability {H H' : SubTemporalGraph G} {x : H.Verts} {y z : H'.Verts} {n m : ℕ}
    [H.IsSymm] [H'.IsSymm] [G.IsSymm] [G.IsLoopless]
    (h₀ : H.IsClique)
    (h₁ : G.Adj y x n)
    (h₂ : G.Adj z x m)
    (h₃ : H.EarliestEdge y x n)
    (h₄ : H.LatestEdge z x m)
    (h₅ : H'.IsSpannerOf (H.dismount x)) :
    H'.mount x h₁ h₂ |>.IsSpannerOf H := by
  have heq : (H'.mount x h₁ h₂).Verts = H.Verts := by simp only [mount_verts, h₅.right.choose,
    induce_Verts, Set.union_singleton, Subtype.coe_prop, Set.insert_diff_self_of_mem]
  have hle : H'.mount x h₁ h₂ ≤ H := by
    apply le_iff_edgeSet_and_verts.mpr
    constructor
    · rw [H'.mount_edgeSet]
      have hsplit : H.EdgeSet = H.EdgeSet ∪ H.EdgeSet := by simp
      rw [hsplit]
      apply Set.union_subset_union
      · apply edgeSet_le
        apply le_trans h₅.left dismount_le
      · have : (s(↑z, ↑x), m) ∈ H.EdgeSet := by
          rw [H.mem_edgeSet]
          apply h₄.left
        have : (s(↑y, ↑x), n) ∈ H.EdgeSet := by
          rw [H.mem_edgeSet]
          apply h₃.left
        grind
    · simp only [mount_verts, h₅.right.choose, induce_Verts, Set.union_singleton, Subtype.coe_prop,
      Set.insert_diff_self_of_mem, subset_refl]
  have htc : (H'.mount x h₁ h₂).TemporallyConnected := by
    apply mount_tc H'
    · apply earliestEdge_of_ge _ h₃
      · exact (mount_edge H' h₁ h₂).symm
      · trivial
    · apply latestEdge_of_ge _ h₄
      · apply mount_edge'
      · trivial
    · have htc : H.dismount x |>.IsClique := by
        apply dismount_clique
        exact h₀
      rw [isClique_iff_coe] at htc
      apply temporallyConnected_of_isClique at htc
      rw [←temporallyConnected_iff] at htc
      unfold TemporallyConnected at htc ⊢
      intro u v
      have := htc ⟨u, by grind only [h₅.right.choose]⟩ ⟨v, by grind only [h₅.right.choose]⟩
      obtain ⟨_, h⟩ := h₅.right
      exact h _ _ this
  constructor
  · trivial
  · use heq
    intro u v _
    simpa using htc ⟨u, by grind only⟩ ⟨v, by grind only⟩

end Mount

section Mount2

def twoHopMount (H : SubTemporalGraph G) {y y' z z' : H.Verts} {n n' m m' : ℕ} (x : V)
    [G.IsSymm]
    (h₀ : G.Adj x y' n')
    (h₁ : G.Adj y' y n)
    (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) :
    G.SubTemporalGraph :=
  H.addVerts {x}
    |>.addEdgeSymm h₀ (by simp)
    |>.addEdgeSymm h₁ (by simp)
    |>.addEdgeSymm h₂ (by simp)
    |>.addEdgeSymm h₃ (by simp)

@[simp]
lemma twoHopMount_verts (H : SubTemporalGraph G) {y y' z z' : H.Verts} {n n' m m' : ℕ} (x : V)
    [G.IsSymm]
    (h₀ : G.Adj x y' n')
    (h₁ : G.Adj y' y n)
    (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) :
    (H.twoHopMount x h₀ h₁ h₂ h₃).Verts = H.Verts ∪ {x} := by
  simp only [twoHopMount, addEdgeSymm_verts, induce_Verts, Set.union_singleton]

-- Same as `mount_isSymm`: resolution stops at the `def`, so unfold the four `addEdgeSymm`
-- layers once and let the `addEdgeSymm_isSymm`/`addVerts_isSymm` instances take over.
instance twoHopMount_isSymm (H : SubTemporalGraph G) {y y' z z' : H.Verts} {n n' m m' : ℕ} (x : V)
    [H.IsSymm] [G.IsSymm]
    (h₀ : G.Adj x y' n')
    (h₁ : G.Adj y' y n)
    (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) :
    (H.twoHopMount x h₀ h₁ h₂ h₃).IsSymm := by
  unfold twoHopMount
  infer_instance

@[simp]
lemma mem_twoHopMount_verts {H : SubTemporalGraph G} {y y' z z' : H.Verts} {n n' m m' : ℕ} {x : V}
    [G.IsSymm]
    {h₀ : G.Adj x y' n'}
    {h₁ : G.Adj y' y n}
    {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m}
    (x' : H.Verts) :
    ↑x' ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).Verts := by
  simp [twoHopMount_verts]

@[simp]
lemma twoHopMount_edgeSet (H : SubTemporalGraph G) {y y' z z' : H.Verts} {n n' m m' : ℕ} (x : V)
    [G.IsSymm] [G.IsLoopless]
    (h₀ : G.Adj x y' n')
    (h₁ : G.Adj y' y n)
    (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) :
    (H.twoHopMount x h₀ h₁ h₂ h₃).EdgeSet =
    H.EdgeSet ∪ {⟨s(z', z), m⟩,  ⟨s(x, z'), m'⟩, ⟨s(y',y), n⟩, ⟨s(x,y'), n'⟩} := by
  simp [twoHopMount, addEdgeSymm_edgeSet, addVerts_edgeSet]

-- The four edges below are the ones `twoHopMount` inserts directly, so each is obtained by
-- lifting `addEdgeSymm_edge` along the later `addEdgeSymm_le` layers: no symmetry needed.
lemma twoHopMount_edge {H : SubTemporalGraph G} {y y' z z' : H.Verts} {n n' m m' : ℕ} {x : V}
    [G.IsSymm]
    {h₀ : G.Adj x y' n'}
    {h₁ : G.Adj y' y n}
    {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m} :
    (H.twoHopMount x h₀ h₁ h₂ h₃).Adj x y' n' := by
  rw [twoHopMount]
  exact addEdgeSymm_le.right <| addEdgeSymm_le.right <| addEdgeSymm_le.right addEdgeSymm_edge

lemma twoHopMount_edge' {H : SubTemporalGraph G} {y y' z z' : H.Verts} {n n' m m' : ℕ} {x : V}
    [G.IsSymm]
    {h₀ : G.Adj x y' n'}
    {h₁ : G.Adj y' y n}
    {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m} :
    (H.twoHopMount x h₀ h₁ h₂ h₃).Adj x z' m' := by
  rw [twoHopMount]
  exact addEdgeSymm_le.right addEdgeSymm_edge

lemma twoHopMount_edge'' {H : SubTemporalGraph G} {y y' z z' : H.Verts} {n n' m m' : ℕ} {x : V}
    [G.IsSymm]
    {h₀ : G.Adj x y' n'}
    {h₁ : G.Adj y' y n}
    {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m} :
    (H.twoHopMount x h₀ h₁ h₂ h₃).Adj y' y n := by
  rw [twoHopMount]
  exact addEdgeSymm_le.right <| addEdgeSymm_le.right addEdgeSymm_edge

lemma twoHopMount_edge''' {H : SubTemporalGraph G} {y y' z z' : H.Verts} {n n' m m' : ℕ} {x : V}
    [G.IsSymm]
    {h₀ : G.Adj x y' n'}
    {h₁ : G.Adj y' y n}
    {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m} :
    (H.twoHopMount x h₀ h₁ h₂ h₃).Adj z' z m := by
  rw [twoHopMount]
  exact addEdgeSymm_edge

@[simp]
lemma twoHopMount_le {H : SubTemporalGraph G} {y y' z z' : H.Verts} {n n' m m' : ℕ} {x : V}
    [G.IsSymm]
    {h₀ : G.Adj x y' n'}
    {h₁ : G.Adj y' y n}
    {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m} :
    H ≤ H.twoHopMount x h₀ h₁ h₂ h₃ :=
  addVerts_le' H {x}
    |>.trans (addEdgeSymm_le' _ h₀ (by simp))
    |>.trans (addEdgeSymm_le' _ h₁ (by simp))
    |>.trans (addEdgeSymm_le' _ h₂ (by simp))
    |>.trans (addEdgeSymm_le' _ h₃ (by simp))

theorem twoHopMount_TC (H : SubTemporalGraph G) {y y' z z' : H.Verts} {n n' m m' : ℕ} (x : V)
    [H.IsSymm] [G.IsSymm]
    (h₀ : G.Adj x y' n')
    (h₁ : G.Adj y' y n)
    (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m)
    (h₄ : (H.twoHopMount x h₀ h₁ h₂ h₃).EarliestEdge y y' n ∧ n' ≤ n)
    (h₅ : (H.twoHopMount x h₀ h₁ h₂ h₃).LatestEdge z z' m ∧ m ≤ m') :
    H.TemporallyConnected → (H.twoHopMount x h₀ h₁ h₂ h₃).TemporallyConnected := by
  have hReach : ∀ x' y', H.Reachable x' y' → (twoHopMount H x h₀ h₁ h₂ h₃).Reachable
    ⟨x', by simp [twoHopMount_verts]⟩
    ⟨y', by simp [twoHopMount_verts]⟩
    := reachable_of_le_reachable twoHopMount_le
  intro htc
  have hx  : x ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).Verts   := by simp
  have hy  : ↑y ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).Verts  := by simp
  have hy' : ↑y' ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).Verts := by simp
  have hz  : ↑z ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).Verts  := by simp
  have hz' : ↑z' ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).Verts := by simp
  simp only [TemporallyConnected, Reachable, Subtype.forall, twoHopMount_verts, Set.union_singleton,
    Set.mem_insert_iff]
  intro a ha b hb
  apply Or.elim ha
  · intro heq
    apply Or.elim hb
    · intro heq'
      simp only [heq, heq', reachable_of_self]
    · intro hb
      simp only [heq]
      have hb' : ↑b ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).Verts := mem_twoHopMount_verts ⟨b, hb⟩
      apply @reachable_of_extended_earliestEdge _ _ (H.twoHopMount x h₀ h₁ h₂ h₃)
        ⟨y, hy⟩ ⟨y', hy'⟩ ⟨x, hx⟩ _ _ inferInstance h₄.left twoHopMount_edge
        h₄.right ⟨b, hb'⟩
      apply hReach y ⟨b, hb⟩
      apply htc
  · intro ha
    apply Or.elim hb
    · intro heq
      simp only [heq]
      have ha' : ↑a ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).Verts := mem_twoHopMount_verts ⟨a, ha⟩
      apply @reachable_of_extended_latestEdge _ _ (H.twoHopMount x h₀ h₁ h₂ h₃)
        ⟨z, hz⟩ ⟨z', hz'⟩ ⟨x, hx⟩ _ _ inferInstance h₅.left
        twoHopMount_edge'.symm h₅.right ⟨a, ha'⟩
      apply hReach ⟨a, ha⟩ z
      apply htc
    · intro hb
      apply hReach ⟨a, ha⟩ ⟨b, hb⟩
      apply htc

instance {H : SubTemporalGraph G} [h₀ : Finite H.EdgeSet] {y y' z z' : H.Verts} {n n' m m' : ℕ}
    {x : V} [G.IsSymm] [G.IsLoopless]
    {h₁ : G.Adj x y' n'}
    {h₂ : G.Adj y' y n}
    {h₃ : G.Adj x z' m'}
    {h₄ : G.Adj z' z m} :
    Finite (H.twoHopMount x h₁ h₂ h₃ h₄).EdgeSet := by
  conv =>
    rhs ; rw [H.twoHopMount_edgeSet x h₁ h₂ h₃ h₄]
  apply Set.Finite.union
  · trivial
  · simp only [Set.finite_insert, Set.finite_singleton]

theorem twoHopMount_size {H : SubTemporalGraph G} [Fintype H.EdgeSet] {y y' z z' : H.Verts}
    {n n' m m' : ℕ}
    {x : V} [G.IsSymm] [G.IsLoopless]
    {h₀ : G.Adj x y' n'}
    {h₁ : G.Adj y' y n}
    {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m}
    [Fintype (H.twoHopMount x h₀ h₁ h₂ h₃).EdgeSet] :
    Fintype.card (H.twoHopMount x h₀ h₁ h₂ h₃).EdgeSet ≤ Fintype.card H.EdgeSet + 4 := by
  conv => lhs ; simp only [H.twoHopMount_edgeSet x h₀ h₁ h₂ h₃]
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  have hle₀ :
      Nat.card ({(s(↑z', ↑z), m), (s(x, ↑z'), m'),
      (s(↑y', ↑y), n), (s(x, ↑y'), n')} : Set ((Sym2 V) × ℕ)) ≤ 4 := by
    have h :  4 = 1 + 1 + 1 + 1 := by simp only [Nat.reduceAdd]
    have heq₀ : Nat.card ({(s(↑z', ↑z), m)} : Set (Sym2 V × ℕ)) = 1 := by simp
    have heq₁ : Nat.card ({(s(x, z'), m')} : Set (Sym2 V × ℕ)) = 1 := by simp
    have heq₂ : Nat.card ({(s(↑y', ↑y), n)} : Set (Sym2 V × ℕ)) = 1 := by simp
    have heq₃ : Nat.card ({(s(x, ↑y'), n')} : Set (Sym2 V × ℕ)) = 1 := by simp
    grind only [Set.card_union_le, !Set.insert_eq]
  have hle₁ :
      Nat.card ↑(H.EdgeSet ∪ {⟨s(z', z), m⟩,  ⟨s(x, z'), m'⟩, ⟨s(y',y), n⟩, ⟨s(x,y'), n'⟩})
      ≤ Nat.card H.EdgeSet  + Nat.card ({(s(↑z', ↑z), m), (s(x, ↑z'), m'), (s(↑y', ↑y), n),
        (s(x, ↑y'), n')} : Set ((Sym2 V) × ℕ)) := by
    simp only [Set.card_union_le]
  lia

theorem twoHopDismountability {H H' : SubTemporalGraph G} {x : H.Verts} {y y' z z' : H'.Verts}
    {n n' m m' : ℕ}
    [H.IsSymm] [H'.IsSymm] [G.IsSymm] [G.IsLoopless]
    (h₀ : H.IsClique)
    (h₁ : G.Adj x y' n')
    (h₂ : G.Adj y' y n)
    (h₃ : G.Adj x z' m')
    (h₄ : G.Adj z' z m)
    (h₅ : H.EarliestEdge y y' n ∧ n' ≤ n ∧ H.Adj x y' n')
    (h₆ : H.LatestEdge z z' m ∧ m ≤ m' ∧ H.Adj x z' m')
    (h₇ : H'.IsSpannerOf (H.dismount x)) :
    H'.twoHopMount x h₁ h₂ h₃ h₄ |>.IsSpannerOf H := by
  have heq : (H'.twoHopMount x h₁ h₂ h₃ h₄).Verts = H.Verts := by
    simp [twoHopMount_verts, h₇.right.choose]
  have hle : (H'.twoHopMount x h₁ h₂ h₃ h₄) ≤ H := by
    apply le_iff_edgeSet_and_verts.mpr
    constructor
    · rw [H'.twoHopMount_edgeSet x h₁ h₂ h₃ h₄]
      have hsplit : H.EdgeSet = H.EdgeSet ∪ H.EdgeSet := by simp
      rw [hsplit]
      apply Set.union_subset_union
      · apply edgeSet_le
        apply le_trans h₇.left dismount_le
      · have : (s(↑z, ↑z'), m) ∈ H.EdgeSet := by
          rw [H.mem_edgeSet]
          apply h₆.1.1
        have : (s(↑x, ↑z'), m') ∈ H.EdgeSet := by
          rw [H.mem_edgeSet]
          apply h₆.2.2
        have : (s(↑y, ↑y'), n) ∈ H.EdgeSet := by
          rw [H.mem_edgeSet]
          apply h₅.1.1
        have : (s(↑x, ↑y'), n') ∈ H.EdgeSet := by
          rw [H.mem_edgeSet]
          apply h₅.2.2
        grind
    · exact heq.le
  have htc : (H'.twoHopMount x h₁ h₂ h₃ h₄).TemporallyConnected := by
    apply twoHopMount_TC H' ↑x
    · apply And.intro
      · apply earliestEdge_of_ge _ h₅.left
        · exact twoHopMount_edge''.symm
        · trivial
      · exact h₅.2.1
    · apply And.intro
      · apply latestEdge_of_ge _ h₆.left
        · exact twoHopMount_edge'''.symm
        · trivial
      · exact h₆.2.1
    · have hclique : H.dismount x |>.IsClique := by
        apply dismount_clique
        exact h₀
      rw [isClique_iff_coe] at hclique
      apply temporallyConnected_of_isClique at hclique
      rw [←temporallyConnected_iff] at hclique
      unfold TemporallyConnected at hclique ⊢
      intro u v
      have := hclique ⟨u, by grind only [h₇.right.choose]⟩ ⟨v, by grind only [h₇.right.choose]⟩
      obtain ⟨_, h⟩ := h₇.right
      exact h _ _ this
  constructor
  · trivial
  · use heq
    intro u v _
    simpa using htc ⟨u, by grind only⟩ ⟨v, by grind only⟩

end Mount2

end SubTemporalGraph

end TemporalGraph
