/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic
import TemporalGraph.SubTemporalGraph
import TemporalGraph.Connectivity.SubTemporalGraph

universe u
variable {V : Type u} {G : SimpleTemporalGraph V}

namespace SimpleTemporalGraph

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

end Dismount

section Mount

def mount (H : SubTemporalGraph G) {y z : H.Verts} {n m : ℕ} (x : V)
    (h₀ : G.Adj y x n)
    (h₁ : G.Adj z x m) :
    G.SubTemporalGraph :=
((H.addVerts {x}).addEdge h₀ (by simp)).addEdge h₁ (by simp)

@[simp]
lemma mount_verts {H : SubTemporalGraph G} {x : V} {y z : H.Verts} {n m : ℕ}
    (h₀ : G.Adj y x n)
    (h₁ : G.Adj z x m) :
    (mount H x h₀ h₁).Verts = H.Verts ∪ {x} := by
  rw [mount, addEdge_verts, addEdge_verts, addVerts_verts]

@[simp]
lemma mem_mount_verts {H : SubTemporalGraph G} {x : V} {y z : H.Verts} {n m : ℕ}
    {h₀ : G.Adj y x n}
    {h₁ : G.Adj z x m}
    (x' : H.Verts) :
    x'.val ∈ (mount H x h₀ h₁).Verts := by simp [mount_verts]

lemma mount_edge (H : SubTemporalGraph G) {x : V} {y z : H.Verts} {n m : ℕ}
    (h₀ : G.Adj y x n)
    (h₁ : G.Adj z x m) :
    (mount H x h₀ h₁).Adj x y n := by
  simp only [mount, addEdge, induce_Verts, Set.union_singleton, induce_Adj, Set.mem_insert_iff,
    true_or, true_and, and_true, and_self, or_true]

lemma mount_edge' (H : SubTemporalGraph G) {x : V} {y z : H.Verts} {n m : ℕ}
    (h₀ : G.Adj y x n)
    (h₁ : G.Adj z x m) :
    (mount H x h₀ h₁).Adj z x m := by
  rw [mount]
  apply addEdge_edge

lemma mount_le {H : SubTemporalGraph G} {x : V} {y z : H.Verts} {n m : ℕ}
    {h₀ : G.Adj y x n}
    {h₁ : G.Adj z x m} :
    H ≤ H.mount x h₀ h₁ := by
  unfold mount
  have h := addVerts_le' H {x}
  have h' := h.trans <| addEdge_le' (H.addVerts {x}) h₀ (by simp)
  exact le_trans h' addEdge_le

@[simp]
lemma mount_edgeSet (H : SubTemporalGraph G) {x : V} {y z : H.Verts} {n m : ℕ}
    (h₀ : G.Adj y x n)
    (h₁ : G.Adj z x m) :
    (H.mount x h₀ h₁).EdgeSet = H.EdgeSet ∪ {⟨s(z,x), m⟩, ⟨s(y,x), n⟩} := by
  simp [mount, addEdge_edgeSet, addVerts_edgeSet]

theorem mount_tc (H : SubTemporalGraph G) {x : V} {y z : H.Verts} {n m : ℕ}
    (h₀ : G.Adj y x n)
    (h₁ : G.Adj z x m)
    (h₂ : (mount H x h₀ h₁).EarliestEdge y x n)
    (h₃ : (mount H x h₀ h₁).LatestEdge z x m) :
    H.TemporallyConnected → (mount H x h₀ h₁).TemporallyConnected := by
  have hReach : ∀ x' y', H.Reachable x' y' → (mount H x h₀ h₁).Reachable
    ⟨x', by simp [mount_verts]⟩
    ⟨y', by simp [mount_verts]⟩
    := reachable_of_subTempGraph_reachable' mount_le
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
      simpa using @SimpleTemporalGraph.self_reachable _ ((mount H x h₀ h₁).coe) ⟨x, _⟩
    · intro hy'₀
      have hy'₁ : y' ∈ (mount H x h₀ h₁).Verts := by simp [hy']
      apply @reachable_of_earliestEdge _ _ (mount H x h₀ h₁) ⟨y, _⟩ ⟨x, _⟩ n h₂ ⟨y', _⟩
      exact hReach ⟨y, _⟩ ⟨y', hy'₀⟩ <| hTC _ _
  · intro hx' ; apply hy'.elim
    · intro heq
      conv => rhs ; lhs ; rw [heq]
      apply @reachable_of_latestEdge _ _ (mount H x h₀ h₁) ⟨z, _⟩ ⟨x, _⟩ m h₃ ⟨x', _⟩
      exact hReach ⟨x', hx'⟩ ⟨z, _⟩ <| hTC _ _
    · intro hy' ; exact hReach ⟨x', hx'⟩ ⟨y', hy'⟩ <| hTC _ _

instance {H : SubTemporalGraph G} [h₀ : Finite H.EdgeSet] {x : V} {y z : H.Verts} {n m : ℕ}
    {h₁ : G.Adj y x n}
    {h₂ : G.Adj z x m} :
    Finite (H.mount x h₁ h₂).EdgeSet := by
  conv =>
    rhs ; rw [mount_edgeSet]
  apply Set.Finite.union
  · trivial
  · simp only [Set.finite_insert, Set.finite_singleton]

-- C'est pas beau mais ca marche
theorem card_mount {H : SubTemporalGraph G} [Fintype H.EdgeSet] {x : V} {y z : H.Verts} {n m : ℕ}
    {h₀ : G.Adj y x n}
    {h₁ : G.Adj z x m} :
    Fintype.card (H.mount x h₀ h₁).EdgeSet ≤ Fintype.card H.EdgeSet + 2 := by
  conv => lhs ; simp only [mount_edgeSet]
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
  grind only

end Mount

section Mount2

def mount2 (H : SubTemporalGraph G) {y y' z z' : H.Verts} {n n' m m' : ℕ} (x : V)
    (h₀ : G.Adj x y' n')
    (h₁ : G.Adj y' y n)
    (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) :
    G.SubTemporalGraph :=
  H.addVerts {x}
    |>.addEdge h₀ (by simp)
    |>.addEdge h₁ (by simp)
    |>.addEdge h₂ (by simp)
    |>.addEdge h₃ (by simp)

@[simp]
lemma mount2_verts (H : SubTemporalGraph G) {y y' z z' : H.Verts} {n n' m m' : ℕ} (x : V)
    (h₀ : G.Adj x y' n')
    (h₁ : G.Adj y' y n)
    (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) :
    (H.mount2 x h₀ h₁ h₂ h₃).Verts = H.Verts ∪ {x} := by
  simp only [mount2, addEdge_verts, induce_Verts, Set.union_singleton]

@[simp]
lemma mem_mount2_verts {H : SubTemporalGraph G} {y y' z z' : H.Verts} {n n' m m' : ℕ} {x : V}
    {h₀ : G.Adj x y' n'}
    {h₁ : G.Adj y' y n}
    {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m}
    (x' : H.Verts) :
    ↑x' ∈ (H.mount2 x h₀ h₁ h₂ h₃).Verts := by
  simp [mount2_verts]

@[simp]
lemma mount2_edgeSet (H : SubTemporalGraph G) {y y' z z' : H.Verts} {n n' m m' : ℕ} (x : V)
    (h₀ : G.Adj x y' n')
    (h₁ : G.Adj y' y n)
    (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) :
    (H.mount2 x h₀ h₁ h₂ h₃).EdgeSet =
    H.EdgeSet ∪ {⟨s(z', z), m⟩,  ⟨s(x, z'), m'⟩, ⟨s(y',y), n⟩, ⟨s(x,y'), n'⟩} := by
  simp [mount2, addEdge_edgeSet, addVerts_edgeSet]

lemma mount2_edge {H : SubTemporalGraph G} {y y' z z' : H.Verts} {n n' m m' : ℕ} {x : V}
    {h₀ : G.Adj x y' n'}
    {h₁ : G.Adj y' y n}
    {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m} :
    (H.mount2 x h₀ h₁ h₂ h₃).Adj x y' n' := by
  simp [←mem_edgeSet]

lemma mount2_edge' {H : SubTemporalGraph G} {y y' z z' : H.Verts} {n n' m m' : ℕ} {x : V}
    {h₀ : G.Adj x y' n'}
    {h₁ : G.Adj y' y n}
    {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m} :
    (H.mount2 x h₀ h₁ h₂ h₃).Adj x z' m' := by
  simp [←mem_edgeSet]

@[simp]
lemma mount2_le {H : SubTemporalGraph G} {y y' z z' : H.Verts} {n n' m m' : ℕ} {x : V}
    {h₀ : G.Adj x y' n'}
    {h₁ : G.Adj y' y n}
    {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m} :
    H ≤ H.mount2 x h₀ h₁ h₂ h₃ :=
  addVerts_le' H {x}
    |>.trans (addEdge_le' _ h₀ (by simp))
    |>.trans (addEdge_le' _ h₁ (by simp))
    |>.trans (addEdge_le' _ h₂ (by simp))
    |>.trans (addEdge_le' _ h₃ (by simp))

theorem mount2_TC (H : SubTemporalGraph G) {y y' z z' : H.Verts} {n n' m m' : ℕ} (x : V)
    (h₀ : G.Adj x y' n')
    (h₁ : G.Adj y' y n)
    (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m)
    (h₄ : (H.mount2 x h₀ h₁ h₂ h₃).EarliestEdge y y' n ∧ n' ≤ n)
    (h₅ : (H.mount2 x h₀ h₁ h₂ h₃).LatestEdge z z' m ∧ m ≤ m') :
    H.TemporallyConnected → (H.mount2 x h₀ h₁ h₂ h₃).TemporallyConnected := by
  have hReach : ∀ x' y', H.Reachable x' y' → (mount2 H x h₀ h₁ h₂ h₃).Reachable
    ⟨x', by simp [mount2_verts]⟩
    ⟨y', by simp [mount2_verts]⟩
    := reachable_of_subTempGraph_reachable' mount2_le
  intro htc
  have hx  : x ∈ (H.mount2 x h₀ h₁ h₂ h₃).Verts   := by simp
  have hy  : ↑y ∈ (H.mount2 x h₀ h₁ h₂ h₃).Verts  := by simp
  have hy' : ↑y' ∈ (H.mount2 x h₀ h₁ h₂ h₃).Verts := by simp
  have hz  : ↑z ∈ (H.mount2 x h₀ h₁ h₂ h₃).Verts  := by simp
  have hz' : ↑z' ∈ (H.mount2 x h₀ h₁ h₂ h₃).Verts := by simp
  simp only [TemporallyConnected, Reachable, Subtype.forall, mount2_verts, Set.union_singleton,
    Set.mem_insert_iff]
  intro a ha b hb
  apply Or.elim ha
  · intro heq
    apply Or.elim hb
    · intro heq'
      simp only [heq, heq', self_reachable]
    · intro hb
      simp only [heq]
      have hb' : ↑b ∈ (H.mount2 x h₀ h₁ h₂ h₃).Verts := mem_mount2_verts ⟨b, hb⟩
      apply @reachable_of_???? _ _ (H.mount2 x h₀ h₁ h₂ h₃) ⟨y, hy⟩ ⟨y', hy'⟩ ⟨x, hx⟩ _ _
        h₄.left (mount2_edge) h₄.right ⟨b, hb'⟩
      apply hReach y ⟨b, hb⟩
      apply htc
  · intro ha
    apply Or.elim hb
    · intro heq
      simp only [heq]
      have ha' : ↑a ∈ (H.mount2 x h₀ h₁ h₂ h₃).Verts := mem_mount2_verts ⟨a, ha⟩
      apply @reachable_of_????' _ _ (H.mount2 x h₀ h₁ h₂ h₃) ⟨z, hz⟩ ⟨z', hz'⟩ ⟨x, hx⟩ _ _
        h₅.left (mount2_edge'.symm) h₅.right ⟨a, ha'⟩
      apply hReach ⟨a, ha⟩ z
      apply htc
    · intro hb
      apply hReach ⟨a, ha⟩ ⟨b, hb⟩
      apply htc

end Mount2

end SubTemporalGraph

end SimpleTemporalGraph
