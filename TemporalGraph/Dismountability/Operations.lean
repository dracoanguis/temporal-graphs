/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic
import TemporalGraph.Subgraph
import TemporalGraph.Connectivity.Subgraph

/-!
# Dismounting and mounting

This module carries out the inductive step of the spanner construction from Carnevale, Casteigts
& Corsini's revisited dismountability argument (SAND 2025, Theorem 2.1), originally due to
Casteigts, Peters & Schoeters (CPS, ICALP 2019 / JCSS): given a spanner of a clique with a vertex
removed, extend it back to a spanner of the whole clique by re-attaching that vertex through the
few edges that made it dismountable (or two-hop-dismountable) in the first place.

* `dismount` removes a single vertex from a subgraph.
* `mount` adds a vertex back with (at most) its earliest and latest edge, for the one-hop case.
* `twoHopMount` adds a vertex back reached through an intermediate vertex on each side, for the
  two-hop case (`Dismountability/Basic.lean`'s `TwoHopDismountable`).

## Main results

* `TemporalGraph.Subgraph.dismountability` : SAND 2025, Theorem 2.1 (1-hop dismountability);
  dismounting and re-mounting through the earliest and latest edge preserves being a spanner,
  adding at most 2 edges (`mount_size`).
* `TemporalGraph.Subgraph.twoHopDismountability` : SAND 2025, §2.1 (the 2-hop case, unnumbered
  in SAND); the two-hop analogue, adding at most 4 edges (`twoHopMount_size`).
* `ncard_pair_le`, `ncard_le_four` (section `CardHelpers`) : `Set.ncard` bounds on a set given by
  2, resp. 4, elements, shared by the edge-count bounds of `mount`, `twoHopMount` and (in
  `Dismountability/OneSided.lean`) `oneSidedMount`.

## References

* Carnevale, Casteigts & Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025,
  LIPIcs 330, 6:1–6:18, doi:10.4230/LIPIcs.SAND.2025.6, arXiv:2502.01321.
* Casteigts, Peters & Schoeters, *Temporal Cliques Admit Sparse Spanners*, ICALP 2019 / JCSS
  (original source of the argument).
-/

universe u
variable {V : Type u} {G : TemporalGraph V}

namespace TemporalGraph

namespace Subgraph

section CardHelpers

/-- An unordered pair has `Set.ncard` at most 2. Shared by the `mount`/`twoHopMount`/
`oneSidedMount` edge-count bounds below. -/
lemma ncard_pair_le {α : Type*} (a b : α) : ({a, b} : Set α).ncard ≤ 2 := by
  have h1 := Set.ncard_insert_le a ({b} : Set α)
  have h2 := Set.ncard_singleton b
  omega

/-- A set given by (up to) four elements has `Set.ncard` at most 4. Shared by the `twoHopMount`
edge-count bound below. -/
lemma ncard_le_four {α : Type*} (a b c d : α) : ({a, b, c, d} : Set α).ncard ≤ 4 := by
  have h1 := Set.ncard_insert_le a ({b, c, d} : Set α)
  have h2 := Set.ncard_insert_le b ({c, d} : Set α)
  have h3 := Set.ncard_insert_le c ({d} : Set α)
  have h4 := Set.ncard_singleton d
  omega

end CardHelpers

section Dismount

/-- Delete the vertex `x` from `H` (the "dismount" operation). -/
abbrev dismount (H : Subgraph G) (x : V) := H.deleteVerts {x}

/-- Dismounting a vertex from a clique subgraph leaves a clique subgraph. -/
lemma dismount_clique (H : Subgraph G) (x : V) (h₀ : H.IsCliqueSubgraph) :
    (H.dismount x).IsCliqueSubgraph := by
  unfold IsCliqueSubgraph IsClique dismount
  intro y hy z hz hne
  simp only [induce_verts, Set.mem_sdiff, Set.mem_singleton_iff] at hy hz
  have hy' : y ∈ H.verts := hy.1
  have hz' : z ∈ H.verts := hz.1
  have ⟨n, hadj⟩ := h₀ hy' hz' hne
  use n
  simp only [induce_Adj, Set.mem_sdiff, hy', Set.mem_singleton_iff, true_and, hz', hadj, and_true]
  exact ⟨hy.2, hz.2⟩

/-- `H.dismount x` has vertex set `H.verts \ {x}`. -/
@[simp, grind =]
lemma dismount_verts {H : Subgraph G} {x : V} : (H.dismount x).verts = H.verts \ {x} := by
  simp only [induce_verts]

/-- Dismounting a vertex yields a subgraph of the original. -/
@[simp]
lemma dismount_le {H : Subgraph G} {x : V} : (H.dismount x) ≤ H := by
  simp only [deleteVerts_le]

end Dismount

section Mount

/-- Add `x` back to `H`, connected via its earliest edge to `y` and latest edge to `z` (the
"mount" operation). -/
def mount (H : Subgraph G) [G.IsSymm] {y z : V} {n m : ℕ} (hy : y ∈ H.verts) (hz : z ∈ H.verts)
    (x : V) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    G.Subgraph :=
  ((H.addVerts {x}).addEdge h₀ (by simp [hy])).addEdge h₁ (by simp [hz])

/-- `H.mount hy hz x h₀ h₁` has vertex set `H.verts ∪ {x}`. -/
@[simp, grind =]
lemma mount_verts {H : Subgraph G} [G.IsSymm] {x y z : V} {n m : ℕ} (hy : y ∈ H.verts)
    (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H hy hz x h₀ h₁).verts = H.verts ∪ {x} := by
  rw [mount, addEdge_verts, addEdge_verts, addVerts_verts]

/-- `H.mount hy hz x h₀ h₁` is symmetric when `H` and `G` are. -/
-- `mount` is a plain `def`, so instance resolution cannot see the `addEdge`/`addVerts`
-- layers it is built from; this instance unfolds it once and hands the goal back to resolution.
instance mount_isSymm {H : Subgraph G} [H.IsSymm] [G.IsSymm] {x y z : V} {n m : ℕ}
    (hy : y ∈ H.verts) (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H hy hz x h₀ h₁).IsSymm := by
  unfold mount
  infer_instance

/-- Every vertex of `H` remains a vertex of `H.mount hy hz x h₀ h₁`. -/
@[simp]
lemma mem_mount_verts {H : Subgraph G} [G.IsSymm] {x y z : V} {n m : ℕ} {hy : y ∈ H.verts}
    {hz : z ∈ H.verts} {h₀ : G.Adj y x n} {h₁ : G.Adj z x m} {x' : V} (hx' : x' ∈ H.verts) :
    x' ∈ (mount H hy hz x h₀ h₁).verts := by simp [mount_verts, hx']

/-- `H.mount hy hz x h₀ h₁` contains the edge from `x` to `y` at time `n`. -/
lemma mount_edge (H : Subgraph G) [G.IsSymm] {x y z : V} {n m : ℕ} (hy : y ∈ H.verts)
    (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H hy hz x h₀ h₁).Adj x y n := by
  simp only [mount, addEdge, induce_verts, Set.union_singleton, induce_Adj,
    Set.mem_insert_iff, true_or, true_and, and_true, and_self, or_true]

/-- `H.mount hy hz x h₀ h₁` contains the edge from `z` to `x` at time `m`. -/
lemma mount_edge' (H : Subgraph G) [G.IsSymm] {x y z : V} {n m : ℕ} (hy : y ∈ H.verts)
    (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H hy hz x h₀ h₁).Adj z x m := by
  rw [mount]
  apply addEdge_edge

/-- `H` is a subgraph of `H.mount hy hz x h₀ h₁`. -/
lemma mount_le {H : Subgraph G} [G.IsSymm] {x y z : V} {n m : ℕ} (hy : y ∈ H.verts)
    (hz : z ∈ H.verts) {h₀ : G.Adj y x n} {h₁ : G.Adj z x m} :
    H ≤ H.mount hy hz x h₀ h₁ := by
  unfold mount
  have h := addVerts_le' H {x}
  have h' := h.trans <| addEdge_le' (H.addVerts {x}) h₀ (by simp [hy])
  exact le_trans h' addEdge_le

/-- `H.mount hy hz x h₀ h₁` has edge set `H.edgeSet` plus the two new edges `z x` at `m` and `y x`
at `n`. -/
@[simp]
lemma mount_edgeSet (H : Subgraph G) [G.IsSymm] {x y z : V} {n m : ℕ}
    (hy : y ∈ H.verts) (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (H.mount hy hz x h₀ h₁).edgeSet = H.edgeSet ∪ {⟨s(z,x), m⟩, ⟨s(y,x), n⟩} := by
  simp [mount, addEdge_edgeSet, addVerts_edgeSet]

/-- If dismounting `x` from `H` (via its earliest edge to `y` and latest edge to `z`) is
temporally connected, so is `H.mount hy hz x h₀ h₁`, provided those edges are indeed the earliest
and latest edges at `x`. -/
theorem mount_tc (H : Subgraph G) [H.IsSymm] [G.IsSymm] {x y z : V} {n m : ℕ} (hy : y ∈ H.verts)
    (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m)
    (h₂ : (mount H hy hz x h₀ h₁).EarliestEdge y x n)
    (h₃ : (mount H hy hz x h₀ h₁).LatestEdge z x m) :
    H.TemporallyConnectedSubgraph → (mount H hy hz x h₀ h₁).TemporallyConnectedSubgraph := by
  intro hTC
  have hReach : ∀ a b : V, H.Reachable a b → (mount H hy hz x h₀ h₁).Reachable a b :=
    fun _ _ ↦ reachable_of_le_reachable (mount_le hy hz)
  intro a ha b hb
  simp only [mount_verts, Set.union_singleton, Set.mem_insert_iff] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact reachable_of_self _
    · exact reachable_of_earliestEdge h₂ b (hReach y b (hTC y hy b hb))
  · rcases hb with rfl | hb
    · exact reachable_of_latestEdge h₃ a (hReach a z (hTC a ha z hz))
    · exact hReach a b (hTC a ha b hb)

instance {H : Subgraph G} [h₀ : Finite H.edgeSet] [G.IsSymm] {x y z : V}
    {n m : ℕ} {hy : y ∈ H.verts} {hz : z ∈ H.verts} {h₁ : G.Adj y x n} {h₂ : G.Adj z x m} :
    Finite (H.mount hy hz x h₁ h₂).edgeSet := by
  conv =>
    rhs ; rw [H.mount_edgeSet]
  apply Set.Finite.union
  · trivial
  · simp only [Set.finite_insert, Set.finite_singleton]

/-- Instance-free form of `mount_size`: mounting `x` back onto `H` adds at most 2 edges to
`H.edgeSet`'s `Set.ncard`. -/
theorem ncard_edgeSet_mount_le {H : Subgraph G} [G.IsSymm] {x y z : V} {n m : ℕ}
    {hy : y ∈ H.verts} {hz : z ∈ H.verts} {h₀ : G.Adj y x n} {h₁ : G.Adj z x m} :
    (H.mount hy hz x h₀ h₁).edgeSet.ncard ≤ H.edgeSet.ncard + 2 := by
  rw [H.mount_edgeSet]
  have hun := Set.ncard_union_le H.edgeSet ({⟨s(z, x), m⟩, ⟨s(y, x), n⟩} : Set (Sym2 V × ℕ))
  have hcard := ncard_pair_le (⟨s(z, x), m⟩ : Sym2 V × ℕ) ⟨s(y, x), n⟩
  omega

/-- Mounting `x` back onto `H` adds at most 2 edges. -/
theorem mount_size {H : Subgraph G} [G.IsSymm] {x y z : V} {n m : ℕ}
    {hy : y ∈ H.verts} {hz : z ∈ H.verts} {h₀ : G.Adj y x n} {h₁ : G.Adj z x m}
    [Fintype H.edgeSet] [Fintype (H.mount hy hz x h₀ h₁).edgeSet] :
    (H.mount hy hz x h₀ h₁).size ≤ H.size + 2 := by
  rw [size_eq_ncard, size_eq_ncard]
  exact ncard_edgeSet_mount_le

/-- SAND 2025, Theorem 2.1 (1-hop case): re-mounting `x` via its earliest edge to `y` and latest
edge to `z` extends a spanner of `H.dismount x` to a spanner of `H`, when `H` is a clique. -/
theorem dismountability {H H' : Subgraph G} [H.IsSymm] [H'.IsSymm] [G.IsSymm] [G.IsLoopless]
    {x y z : V} (hx : x ∈ H.verts) (hy : y ∈ H'.verts) (hz : z ∈ H'.verts) {n m : ℕ}
    (h₀ : H.IsCliqueSubgraph) (h₁ : G.Adj y x n) (h₂ : G.Adj z x m) (h₃ : H.EarliestEdge y x n)
    (h₄ : H.LatestEdge z x m) (h₅ : H'.IsSpannerOf (H.dismount x)) :
    H'.mount hy hz x h₁ h₂ |>.IsSpannerOf H := by
  have heq : (H'.mount hy hz x h₁ h₂).verts = H.verts := by simp only [mount_verts, h₅.right.1,
    induce_verts, Set.union_singleton, hx, Set.insert_sdiff_self_of_mem]
  have hle : H'.mount hy hz x h₁ h₂ ≤ H := by
    apply le_iff_edgeSet_and_verts.mpr
    constructor
    · rw [H'.mount_edgeSet]
      have hsplit : H.edgeSet = H.edgeSet ∪ H.edgeSet := by simp
      rw [hsplit]
      apply Set.union_subset_union
      · apply edgeSet_le
        apply le_trans h₅.left dismount_le
      · grind
    · simp only [mount_verts, h₅.right.1, induce_verts, Set.union_singleton, hx,
      Set.insert_sdiff_self_of_mem, subset_refl]
  have htc : (H'.mount hy hz x h₁ h₂).TemporallyConnectedSubgraph := by
    apply mount_tc H'
    · apply earliestEdge_of_ge _ h₃
      · exact (mount_edge H' hy hz h₁ h₂).symm
      · trivial
    · apply latestEdge_of_ge _ h₄
      · apply mount_edge'
      · trivial
    · have hdisTC : (H.dismount x).TemporallyConnectedSubgraph :=
        TemporalGraph.temporallyConnected_of_isClique _ (dismount_clique H x h₀)
      intro u hu v hv
      obtain ⟨heqV, hspan⟩ := h₅.right
      rw [heqV] at hu hv
      exact hspan u hu v hv (hdisTC u hu v hv)
  refine ⟨hle, heq, ?_⟩
  intro u hu v hv _
  exact htc u (by rw [heq]; exact hu) v (by rw [heq]; exact hv)

end Mount

section TwoHopMount

/-- Add `x` back to `H`, connected through `y'` on the earliest side and `z'` on the latest side
(the two-hop "mount" operation). -/
def twoHopMount (H : Subgraph G) [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ} (hy : y ∈ H.verts)
    (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) (x : V)
    (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m') (h₃ : G.Adj z' z m) :
    G.Subgraph :=
  H.addVerts {x}
    |>.addEdge h₀ (by simp [hy'])
    |>.addEdge h₁ (by simp [hy', hy])
    |>.addEdge h₂ (by simp [hz'])
    |>.addEdge h₃ (by simp [hz', hz])

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` has vertex set `H.verts ∪ {x}`. -/
@[simp, grind =]
lemma twoHopMount_verts (H : Subgraph G) [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) (x : V)
    (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m') (h₃ : G.Adj z' z m) :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).verts = H.verts ∪ {x} := by
  simp only [twoHopMount, addEdge_verts, induce_verts, Set.union_singleton]

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` is symmetric when `H` and `G` are. -/
-- Same as `mount_isSymm`: resolution stops at the `def`, so unfold the four `addEdge`
-- layers once and let the `addEdge_isSymm`/`addVerts_isSymm` instances take over.
instance twoHopMount_isSymm (H : Subgraph G) [H.IsSymm] [G.IsSymm] {y y' z z' : V}
    {n n' m m' : ℕ} (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts)
    (hz' : z' ∈ H.verts) (x : V) (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).IsSymm := by
  unfold twoHopMount
  infer_instance

/-- Every vertex of `H` remains a vertex of `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃`. -/
@[simp]
lemma mem_twoHopMount_verts {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts)
    {x : V} {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m}
    {x' : V} (hx' : x' ∈ H.verts) :
    x' ∈ (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).verts := by
  simp [twoHopMount_verts, hx']

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` has edge set `H.edgeSet` plus the four new
edges. -/
@[simp]
lemma twoHopMount_edgeSet (H : Subgraph G) [G.IsSymm] {y y' z z' : V}
    {n n' m m' : ℕ} (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts)
    (hz' : z' ∈ H.verts) (x : V) (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).edgeSet =
    H.edgeSet ∪ {⟨s(z', z), m⟩,  ⟨s(x, z'), m'⟩, ⟨s(y',y), n⟩, ⟨s(x,y'), n'⟩} := by
  simp [twoHopMount, addEdge_edgeSet, addVerts_edgeSet]

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` contains the edge from `x` to `y'` at time
`n'`. -/
-- The four edges below are the ones `twoHopMount` inserts directly, so each is obtained by
-- lifting `addEdge_edge` along the later `addEdge_le` layers: no symmetry needed.
lemma twoHopMount_edge {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).Adj x y' n' := by
  rw [twoHopMount]
  exact addEdge_le.right <| addEdge_le.right <| addEdge_le.right addEdge_edge

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` contains the edge from `x` to `z'` at time
`m'`. -/
lemma twoHopMount_edge' {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).Adj x z' m' := by
  rw [twoHopMount]
  exact addEdge_le.right addEdge_edge

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` contains the edge from `y'` to `y` at time `n`. -/
lemma twoHopMount_edge'' {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).Adj y' y n := by
  rw [twoHopMount]
  exact addEdge_le.right <| addEdge_le.right addEdge_edge

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` contains the edge from `z'` to `z` at time `m`. -/
lemma twoHopMount_edge''' {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).Adj z' z m := by
  rw [twoHopMount]
  exact addEdge_edge

/-- `H` is a subgraph of `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃`. -/
@[simp]
lemma twoHopMount_le {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    H ≤ H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃ :=
  addVerts_le' H {x}
    |>.trans (addEdge_le' _ h₀ (by simp [hy']))
    |>.trans (addEdge_le' _ h₁ (by simp [hy', hy]))
    |>.trans (addEdge_le' _ h₂ (by simp [hz']))
    |>.trans (addEdge_le' _ h₃ (by simp [hz', hz]))

/-- If dismounting `x` (via `y'`, `y` on the earliest side and `z'`, `z` on the latest side) is
temporally connected, so is `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃`. -/
theorem twoHopMount_TC (H : Subgraph G) [H.IsSymm] [G.IsSymm] {y y' z z' : V}
    {n n' m m' : ℕ} (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts)
    (hz' : z' ∈ H.verts) (x : V) (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m)
    (h₄ : (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).EarliestEdge y y' n ∧ n' ≤ n)
    (h₅ : (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).LatestEdge z z' m ∧ m ≤ m') :
    H.TemporallyConnectedSubgraph →
      (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).TemporallyConnectedSubgraph := by
  intro hTC
  have hReach : ∀ a b : V, H.Reachable a b →
      (twoHopMount H hy hy' hz hz' x h₀ h₁ h₂ h₃).Reachable a b :=
    fun _ _ ↦ reachable_of_le_reachable (twoHopMount_le hy hy' hz hz')
  intro a ha b hb
  simp only [twoHopMount_verts, Set.union_singleton, Set.mem_insert_iff] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact reachable_of_self _
    · exact reachable_of_extended_earliestEdge h₄.left (twoHopMount_edge hy hy' hz hz')
        h₄.right b (hReach y b (hTC y hy b hb))
  · rcases hb with rfl | hb
    · exact reachable_of_extended_latestEdge h₅.left (twoHopMount_edge' hy hy' hz hz').symm
        h₅.right a (hReach a z (hTC a ha z hz))
    · exact hReach a b (hTC a ha b hb)

instance {H : Subgraph G} [h₀ : Finite H.edgeSet] [G.IsSymm] {y y' z z' : V}
    {n n' m m' : ℕ} {hy : y ∈ H.verts} {hy' : y' ∈ H.verts} {hz : z ∈ H.verts}
    {hz' : z' ∈ H.verts} {x : V} {h₁ : G.Adj x y' n'} {h₂ : G.Adj y' y n} {h₃ : G.Adj x z' m'}
    {h₄ : G.Adj z' z m} :
    Finite (H.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄).edgeSet := by
  conv =>
    rhs ; rw [H.twoHopMount_edgeSet hy hy' hz hz' x h₁ h₂ h₃ h₄]
  apply Set.Finite.union
  · trivial
  · simp only [Set.finite_insert, Set.finite_singleton]

/-- Instance-free form of `twoHopMount_size`: mounting `x` back onto `H` via two hops on each
side adds at most 4 edges to `H.edgeSet`'s `Set.ncard`. -/
theorem ncard_edgeSet_twoHopMount_le {H : Subgraph G} [G.IsSymm]
    {y y' z z' : V} {n n' m m' : ℕ} {hy : y ∈ H.verts} {hy' : y' ∈ H.verts} {hz : z ∈ H.verts}
    {hz' : z' ∈ H.verts} {x : V} {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).edgeSet.ncard ≤ H.edgeSet.ncard + 4 := by
  rw [H.twoHopMount_edgeSet hy hy' hz hz' x h₀ h₁ h₂ h₃]
  have hun := Set.ncard_union_le H.edgeSet
    ({⟨s(z', z), m⟩, ⟨s(x, z'), m'⟩, ⟨s(y', y), n⟩, ⟨s(x, y'), n'⟩} : Set (Sym2 V × ℕ))
  have hcard := ncard_le_four (⟨s(z', z), m⟩ : Sym2 V × ℕ) ⟨s(x, z'), m'⟩ ⟨s(y', y), n⟩
    ⟨s(x, y'), n'⟩
  omega

/-- Mounting `x` back onto `H` via two hops on each side adds at most 4 edges. -/
theorem twoHopMount_size {H : Subgraph G} [G.IsSymm]
    {y y' z z' : V} {n n' m m' : ℕ} {hy : y ∈ H.verts} {hy' : y' ∈ H.verts} {hz : z ∈ H.verts}
    {hz' : z' ∈ H.verts} {x : V} {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m}
    [Fintype H.edgeSet] [Fintype (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).edgeSet] :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).size ≤ H.size + 4 := by
  rw [size_eq_ncard, size_eq_ncard]
  exact ncard_edgeSet_twoHopMount_le

/-- SAND 2025, §2.1 (2-hop case): re-mounting `x` via two hops on each side extends a spanner of
`H.dismount x` to a spanner of `H`, when `H` is a clique. -/
theorem twoHopDismountability {H H' : Subgraph G} [H.IsSymm] [H'.IsSymm] [G.IsSymm] [G.IsLoopless]
    {x y y' z z' : V} (hx : x ∈ H.verts) (hy : y ∈ H'.verts) (hy' : y' ∈ H'.verts)
    (hz : z ∈ H'.verts) (hz' : z' ∈ H'.verts) {n n' m m' : ℕ}
    (h₀ : H.IsCliqueSubgraph) (h₁ : G.Adj x y' n') (h₂ : G.Adj y' y n) (h₃ : G.Adj x z' m')
    (h₄ : G.Adj z' z m) (h₅ : H.EarliestEdge y y' n ∧ n' ≤ n ∧ H.Adj x y' n')
    (h₆ : H.LatestEdge z z' m ∧ m ≤ m' ∧ H.Adj x z' m') (h₇ : H'.IsSpannerOf (H.dismount x)) :
    H'.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄ |>.IsSpannerOf H := by
  have heq : (H'.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄).verts = H.verts := by
    simp [twoHopMount_verts, h₇.right.1, hx]
  have hle : (H'.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄) ≤ H := by
    apply le_iff_edgeSet_and_verts.mpr
    constructor
    · rw [H'.twoHopMount_edgeSet hy hy' hz hz' x h₁ h₂ h₃ h₄]
      have hsplit : H.edgeSet = H.edgeSet ∪ H.edgeSet := by simp
      rw [hsplit]
      apply Set.union_subset_union
      · apply edgeSet_le
        apply le_trans h₇.left dismount_le
      · grind
    · exact heq.le
  have htc : (H'.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄).TemporallyConnectedSubgraph := by
    apply twoHopMount_TC H' hy hy' hz hz' x
    · apply And.intro
      · apply earliestEdge_of_ge _ h₅.left
        · exact (twoHopMount_edge'' hy hy' hz hz').symm
        · trivial
      · exact h₅.2.1
    · apply And.intro
      · apply latestEdge_of_ge _ h₆.left
        · exact (twoHopMount_edge''' hy hy' hz hz').symm
        · trivial
      · exact h₆.2.1
    · have hdisTC : (H.dismount x).TemporallyConnectedSubgraph :=
        TemporalGraph.temporallyConnected_of_isClique _ (dismount_clique H x h₀)
      intro u hu v hv
      obtain ⟨heqV, hspan⟩ := h₇.right
      rw [heqV] at hu hv
      exact hspan u hu v hv (hdisTC u hu v hv)
  refine ⟨hle, heq, ?_⟩
  intro u hu v hv _
  exact htc u (by rw [heq]; exact hu) v (by rw [heq]; exact hv)

end TwoHopMount

end Subgraph

end TemporalGraph
