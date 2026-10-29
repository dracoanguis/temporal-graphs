/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.Subgraph.Operations

/-!
# Edge sets and sizes of subgraphs

The edge set of a subgraph, its size, and the subgraphs built from a temporal graph or a set of
edges.

## Main definitions

* `Subgraph.footprintEdgeSet`, `Subgraph.edgeSetToFootprintEdgeSet` : the edges of `H` with the
  times forgotten, and the map onto them.
* `Subgraph.order` : the number of vertices of `H`.
* `TemporalGraph.toSubgraph`, `Subgraph.fromEdgeSet` : the subgraph given by a temporal graph below
  `G`, resp. by a set of edges.

## Main results

* Edge set: `edgeSet_mono`, `edgeSet_subset`, `sup_edgeSet`, `addEdge_edgeSet`,
  `le_iff_edgeSet_and_verts`, and `edgeSetToFootprintEdgeSet_bijective` (for a symmetric, simple
  subgraph, edges and footprint edges are in bijection).
* Size: the `Set.ncard` forms `ncard_edgeSet_of_simple`, `ncard_edgeSet_addEdge`,
  `ncard_edgeSet_addEdge_le`, `ncard_edgeSet_addVerts`, `order_eq_ncard`, free of `Fintype`
  hypotheses, and their `size` counterparts.
* `Subgraph.fromEdgeSet_eq`, `fromEdgeSet_le`, `fromEdgeSet_mono`, `adj_of_fromEdgeSet_le` : the
  subgraph built from a set of edges of `H` lies in `H`, and grows with the set.
* `Subgraph.exists_matchingEdges` : a family of unique partners `a ↦ (v, n)` over a finite set `A`
  yields a set of at most `|A|` edges `(s(v, a), n)`.
-/

@[expose] public section

universe u

namespace TemporalGraph

namespace Subgraph

variable {V : Type u} {G : TemporalGraph V}

section edgeSet

/-- `⊥ : Subgraph G` has no edges. -/
@[simp, grind =]
theorem bot_edgeSet : (⊥ : Subgraph G).edgeSet = ∅ := by
  ext ⟨p, n⟩
  simp only [TemporalGraph.edgeSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, y, -, hadj⟩
  exact hadj

/-- An adjacency of `H` gives the corresponding undirected edge in `H.edgeSet`. This direction
is orientation-free: it needs neither symmetry of `H` nor looplessness of `G` (it is the `Or.inl`
direction of `mem_edgeSet_iff_or`). -/
protected theorem Adj.mem_edgeSet {H : Subgraph G} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    (s(x,y), n) ∈ H.edgeSet :=
  H.mem_edgeSet_iff_or.mpr (Or.inl h)

/-- The edge set is monotone: `H ≤ H'` implies `H.edgeSet ⊆ H'.edgeSet`. -/
@[simp]
lemma edgeSet_mono {H : Subgraph G} {H' : Subgraph G} (h₀ : H ≤ H') :
    H.edgeSet ⊆ H'.edgeSet := by
  intro _ ⟨x, y, hp, h⟩
  exact ⟨x, y, hp, h₀.right h⟩

/-- The edges of a subgraph of `G` are edges of `G` (analogue of Mathlib's
`SimpleGraph.Subgraph.edgeSet_subset`). -/
lemma edgeSet_subset (H : Subgraph G) : H.edgeSet ⊆ G.edgeSet :=
  fun _ ⟨x, y, hp, h⟩ ↦ ⟨x, y, hp, H.adj_sub h⟩

/-- The edges of a union of subgraphs are the union of their edges. -/
@[simp]
theorem sup_edgeSet (H₁ H₂ : Subgraph G) : (H₁ ⊔ H₂).edgeSet = H₁.edgeSet ∪ H₂.edgeSet := by
  ext ⟨p, n⟩
  induction p using Sym2.ind with
  | _ x y =>
    simp only [TemporalGraph.mem_edgeSet_iff_or, sup_adj, Set.mem_union, or_or_or_comm]

/-- For `H'` symmetric, `H ≤ H'` iff `H`'s edges and vertices are among `H'`'s. -/
lemma le_iff_edgeSet_and_verts {H H' : Subgraph G} [H'.IsSymm] :
    H ≤ H' ↔ H.edgeSet ⊆ H'.edgeSet ∧ H.verts ⊆ H'.verts := by
  constructor
  · intro h
    exact ⟨edgeSet_mono h, h.left⟩
  · intro h
    refine ⟨h.right, fun {_ _ _} hadj ↦ ?_⟩
    -- the edge of `H` is an edge of `H'`, and `H'` is symmetric
    rw [← H'.mem_edgeSet]
    exact h.left (Adj.mem_edgeSet hadj)

/-- Adding an edge inserts the corresponding undirected edge into the edge set. -/
@[simp]
lemma addEdge_edgeSet (H : Subgraph G) {x y : V} {n : ℕ}
    [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts} :
    (H.addEdge h₀ h₁).edgeSet = insert ⟨s(x,y), n⟩ H.edgeSet := by
  ext ⟨p, n'⟩
  induction p using Sym2.ind with
  | _ a b =>
    simp only [Set.mem_insert_iff, Prod.mk.injEq, TemporalGraph.mem_edgeSet_iff_or, addEdge,
      Sym2.eq_iff]
    tauto

instance {H : Subgraph G} [h : Finite H.edgeSet] {x y : V} {n : ℕ}
    [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts} :
    Finite (H.addEdge h₀ h₁).edgeSet := by
  rw [H.addEdge_edgeSet]
  infer_instance

/-- Adding vertices does not change the edge set. -/
@[simp]
lemma addVerts_edgeSet {H : Subgraph G} {s : Set V} :
    (H.addVerts s).edgeSet = H.edgeSet := by
  ext ⟨p, n'⟩
  constructor
  · rintro ⟨a, b, hp, _, _, hadj⟩
    exact ⟨a, b, hp, hadj⟩
  · rintro ⟨a, b, hp, hadj⟩
    exact ⟨a, b, hp, Or.inl (H.edge_vert hadj), Or.inl (H.edge_vert' hadj), hadj⟩

instance {H : Subgraph G} {s : Set V} [h₀ : Finite H.edgeSet] :
    Finite (H.addVerts s).edgeSet := by
  rw [addVerts_edgeSet]
  exact h₀

/-- The underlying simple-graph edge set of `H`: pairs `s(x, y)` such that `H` has an adjacency
between `x` and `y` at some time. -/
def footprintEdgeSet (H : Subgraph G) : Set (Sym2 V) :=
  {p | ∃ n x y, p = s(x,y) ∧ H.Adj x y n}

/-- The map from `H`'s time-stamped edge set to its footprint edge set, forgetting the time. -/
def edgeSetToFootprintEdgeSet (H : Subgraph G) : H.edgeSet → H.footprintEdgeSet :=
  fun x ↦ ⟨x.val.fst, by
    obtain ⟨a, b, hp, hadj⟩ := x.2
    exact ⟨x.val.snd, a, b, hp, hadj⟩⟩

/-- `edgeSetToFootprintEdgeSet` is surjective: every footprint edge comes from some time-stamped
edge. -/
lemma edgeSetToFootprintEdgeSet_surjective (H : Subgraph G) :
    Function.Surjective H.edgeSetToFootprintEdgeSet := by
  intro x
  obtain ⟨n, a, b, hp, hadj⟩ := x.prop
  exact ⟨⟨(x.1, n), a, b, hp, hadj⟩, rfl⟩

/-- For a symmetric, simple subgraph, `edgeSetToFootprintEdgeSet` is injective: at most one time
realizes each undirected edge. -/
lemma edgeSetToFootprintEdgeSet_injective (H : Subgraph G) [H.IsSymm]
    (h₀ : H.IsSimple) :
    Function.Injective H.edgeSetToFootprintEdgeSet := by
  intro x y h
  obtain ⟨a, b, hp, hadj⟩ := x.2
  obtain ⟨a', b', hp', hadj'⟩ := y.2
  simp only [edgeSetToFootprintEdgeSet, Subtype.mk.injEq] at h
  ext
  · exact Sym2.ext_iff.mp h _
  · -- the two edges have the same endpoints, in the same or in the reverse order; in both cases
    -- simplicity gives equal times
    rcases Sym2.eq_iff.mp (hp.symm.trans (h.trans hp')) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h₀ hadj hadj'
    · exact h₀ hadj (H.adj_symm hadj')

/-- For a symmetric, simple subgraph, `edgeSetToFootprintEdgeSet` is a bijection between the
edge set and the footprint edge set. -/
lemma edgeSetToFootprintEdgeSet_bijective (H : Subgraph G) [H.IsSymm]
    (h₀ : H.IsSimple) :
    Function.Bijective H.edgeSetToFootprintEdgeSet :=
  ⟨H.edgeSetToFootprintEdgeSet_injective h₀, H.edgeSetToFootprintEdgeSet_surjective⟩

end edgeSet

section Size

/-- The number of vertices of `H`, for `H.verts` a `Fintype`. -/
def order (H : Subgraph G) [Fintype H.verts] := Fintype.card H.verts

/-- `order` is `Set.ncard` of `H.verts`: the instance-free form. -/
theorem order_eq_ncard (H : Subgraph G) [Fintype H.verts] : H.order = H.verts.ncard :=
  Set.fintypeCard_eq_ncard H.verts

/-- Instance-free form of `size_of_simple`: with no finiteness hypothesis needed, `H.edgeSet` and
`H.footprintEdgeSet` have the same `Set.ncard` when `H` is symmetric and simple. -/
lemma ncard_edgeSet_of_simple (H : Subgraph G) [H.IsSymm] (h₀ : H.IsSimple) :
    H.edgeSet.ncard = H.footprintEdgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.ofBijective _ (H.edgeSetToFootprintEdgeSet_bijective h₀))

/-- For a symmetric, simple subgraph with finitely many edges, `H.size` equals the cardinality of
its footprint edge set. -/
theorem size_of_simple (H : Subgraph G) [H.IsSymm] [Fintype H.edgeSet] (h₀ : H.IsSimple) :
    H.size = H.footprintEdgeSet.ncard := by
  rw [size_eq_ncard]
  exact H.ncard_edgeSet_of_simple h₀

/-- Instance-free form of `addEdge_size`: adding an edge not already present increases the edge
set's `Set.ncard` by exactly one. -/
theorem ncard_edgeSet_addEdge (H : Subgraph G) {x y : V} {n : ℕ}
    [H.IsSymm] [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts}
    {h₂ : ¬H.Adj x y n}
    (hfin : H.edgeSet.Finite := by toFinite_tac) :
    (H.addEdge h₀ h₁).edgeSet.ncard = H.edgeSet.ncard + 1 := by
  rw [H.addEdge_edgeSet]
  exact Set.ncard_insert_of_notMem (fun hm ↦ h₂ (H.mem_edgeSet.mp hm)) hfin

/-- Adding an edge not already present increases `H.size` by exactly one. -/
theorem addEdge_size (H : Subgraph G) {x y : V} {n : ℕ}
    [H.IsSymm] [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts}
    {h₂ : ¬H.Adj x y n}
    [Fintype H.edgeSet] [Fintype (H.addEdge h₀ h₁).edgeSet]
    (hfin : H.edgeSet.Finite := by toFinite_tac) :
    (H.addEdge h₀ h₁).size = H.size + 1 := by
  rw [size_eq_ncard, size_eq_ncard]
  exact H.ncard_edgeSet_addEdge (h₂ := h₂) hfin

/-- Instance-free form of `addEdge_size_le`: adding an edge increases the edge set's
`Set.ncard` by at most one. -/
theorem ncard_edgeSet_addEdge_le (H : Subgraph G) {x y : V} {n : ℕ}
    [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts} :
    (H.addEdge h₀ h₁).edgeSet.ncard ≤ H.edgeSet.ncard + 1 := by
  rw [H.addEdge_edgeSet]
  exact Set.ncard_insert_le _ _

/-- Adding an edge increases `H.size` by at most one. -/
theorem addEdge_size_le (H : Subgraph G) {x y : V} {n : ℕ}
    [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts}
    [Fintype H.edgeSet] [Fintype (H.addEdge h₀ h₁).edgeSet] :
    (H.addEdge h₀ h₁).size ≤ H.size + 1 := by
  rw [size_eq_ncard, size_eq_ncard]
  exact H.ncard_edgeSet_addEdge_le

/-- Instance-free form of `addVerts_size`: adding vertices does not change the edge set's
`Set.ncard`. -/
theorem ncard_edgeSet_addVerts {H : Subgraph G} {s : Set V} :
    (H.addVerts s).edgeSet.ncard = H.edgeSet.ncard :=
  congrArg Set.ncard addVerts_edgeSet

/-- Adding vertices does not change `H.size`. -/
@[simp]
theorem addVerts_size {H : Subgraph G} {s : Set V}
    [Fintype H.edgeSet] [Fintype (H.addVerts s).edgeSet] :
    (H.addVerts s).size = H.size := by
  rw [size_eq_ncard, size_eq_ncard]
  exact ncard_edgeSet_addVerts

end Size

end Subgraph

section Construction

variable {V : Type u} {G : TemporalGraph V}

/-- View a `TemporalGraph` `H ≤ G` as a (spanning) `Subgraph G`. The `simps` lemma is restricted to
`verts`: `Adj` is the bare projection `H.Adj` of an opaque `H`, which `simps` cannot unfold, so
`toSubgraph_adj` below restates it by hand. -/
@[simps! verts]
def toSubgraph (H : TemporalGraph V) (h : H ≤ G) : G.Subgraph where
  verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  edge_vert' _ := Set.mem_univ _

/-- Adjacency in `toSubgraph H h` is adjacency in `H`. -/
@[simp, grind =]
theorem toSubgraph_adj (H : TemporalGraph V) (h : H ≤ G) {x y : V} {n : ℕ} :
    (toSubgraph H h).Adj x y n ↔ H.Adj x y n :=
  Iff.rfl

/-- `toSubgraph H h` is spanning. -/
theorem toSubgraph_isSpanning (H : TemporalGraph V) (h : H ≤ G) :
    (toSubgraph H h).IsSpanning :=
  Set.mem_univ

/-- `toSubgraph H h` is symmetric whenever `H` is. -/
instance toSubgraph_isSymm (H : TemporalGraph V) [hs : H.IsSymm] (h : H ≤ G) :
    (toSubgraph H h).IsSymm :=
  hs

namespace Subgraph

/-- The subgraph of `G` spanned by a set `s` of edges; the edges of `s` not in `G.edgeSet` are
ignored. Unlike `TemporalGraph.fromEdgeSet` (in `Basic.lean`, a plain symmetrized `TemporalGraph`),
it lives in the `Subgraph` namespace, so it must be called qualified, as
`Subgraph.fromEdgeSet G s`: dot notation `G.fromEdgeSet` resolves to the `Basic.lean` one. -/
@[simps!]
def fromEdgeSet (G : TemporalGraph V) (s : Set ((Sym2 V) × ℕ)) :
    Subgraph G where
  verts := {x | ∃ (p : s), x ∈ p.1.1}
  Adj x y n := ∃ (a : s), x ∈ a.1.1 ∧ y ∈ a.1.1 ∧ n = a.1.2 ∧ G.Adj x y n
  adj_sub := fun ⟨_, _, _, _, h⟩ ↦ h
  edge_vert := fun ⟨a, hx, _⟩ ↦ ⟨a, hx⟩
  edge_vert' := fun ⟨a, _, hy, _⟩ ↦ ⟨a, hy⟩

/-- `Subgraph.fromEdgeSet G s` is symmetric whenever `G` is. -/
instance fromEdgeSet_isSymm (G : TemporalGraph V) [G.IsSymm] (s : Set ((Sym2 V) × ℕ)) :
    (fromEdgeSet G s).IsSymm := by
  refine IsSymm.of_adj ?_
  rintro n x y ⟨a, hx, hy, hn, hG⟩
  exact ⟨a, hy, hx, hn, hG.symm⟩

/-- If `s` is a set of `G`'s edges, the subgraph built from `s` has edge set exactly `s`. -/
@[simp]
theorem fromEdgeSet_eq {G : TemporalGraph V} [G.IsSymm] [G.IsLoopless]
    {s : Set ((Sym2 V) × ℕ)} (h₀ : s ⊆ G.edgeSet) :
    (fromEdgeSet G s).edgeSet = s := by
  ext ⟨p, n⟩
  constructor
  · rintro ⟨x, y, hp, a, hxa, hya, hna, hG⟩
    have heq : a.1.1 = s(x, y) := a.1.1.mem_and_mem_iff hG.ne |>.mp ⟨hxa, hya⟩
    have hpa : (p, n) = a.1 := Prod.ext (hp.trans heq.symm) hna
    rw [hpa]
    exact a.2
  · intro ha
    obtain ⟨x, y⟩ := p
    exact ⟨x, y, rfl, ⟨(s(x, y), n), ha⟩, Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _, rfl,
      G.mem_edgeSet.mp (h₀ ha)⟩

/-- A subgraph built from edges of `H` lies in `H`. -/
lemma fromEdgeSet_le {H : Subgraph G} [G.IsLoopless] [H.IsSymm] {E : Set (Sym2 V × ℕ)}
    (h₀ : E ⊆ H.edgeSet) : Subgraph.fromEdgeSet G E ≤ H := by
  refine ⟨?_, ?_⟩
  · rintro v ⟨⟨⟨e, n⟩, he⟩, hv⟩
    induction e using Sym2.ind with
    | _ a b =>
      have hadj := H.mem_edgeSet.mp (h₀ he)
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact H.edge_vert hadj
      · exact H.edge_vert' hadj
  · rintro x y n ⟨⟨⟨e, m⟩, he⟩, hx, hy, rfl, hG⟩
    have heq : e = s(x, y) := e.mem_and_mem_iff hG.ne |>.mp ⟨hx, hy⟩
    have hmem := h₀ he
    rw [heq] at hmem
    exact H.mem_edgeSet.mp hmem

/-- `Subgraph.fromEdgeSet` is monotone in the edge set. -/
lemma fromEdgeSet_mono {E E' : Set (Sym2 V × ℕ)} (h₀ : E ⊆ E') :
    Subgraph.fromEdgeSet G E ≤ Subgraph.fromEdgeSet G E' := by
  refine ⟨?_, ?_⟩
  · rintro v ⟨⟨p, hp⟩, hv⟩
    exact ⟨⟨p, h₀ hp⟩, hv⟩
  · rintro x y n ⟨⟨p, hp⟩, hx, hy, hn, hG⟩
    exact ⟨⟨p, h₀ hp⟩, hx, hy, hn, hG⟩

/-- An edge of `E` that lies in `G` is an adjacency of every subgraph above
`Subgraph.fromEdgeSet G E`. -/
lemma adj_of_fromEdgeSet_le {K : Subgraph G} {E : Set (Sym2 V × ℕ)} {a b : V} {n : ℕ}
    (h₀ : Subgraph.fromEdgeSet G E ≤ K) (h₁ : (s(a, b), n) ∈ E) (h₂ : G.Adj a b n) :
    K.Adj a b n :=
  h₀.right ⟨⟨(s(a, b), n), h₁⟩, Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _, rfl, h₂⟩

/-- An edge of `E` that is an arc of `G` is an arc of `Subgraph.fromEdgeSet G E`. -/
lemma adj_fromEdgeSet {E : Set (Sym2 V × ℕ)} {a b : V} {n : ℕ} (h₀ : (s(a, b), n) ∈ E)
    (h₁ : G.Adj a b n) : (Subgraph.fromEdgeSet G E).Adj a b n :=
  adj_of_fromEdgeSet_le le_rfl h₀ h₁

/-- If a relation `R` gives each `a ∈ A` a unique partner `(v, n)` with `v ∈ B` and `R v a n`,
then there is a set `E` of at most `|A|` edges `(s(v, a), n)` that contains every such edge, has an
edge at every `a ∈ A`, and consists only of such edges. -/
lemma exists_matchingEdges {A B : Set V} {R : V → V → ℕ → Prop} (h₀ : A.Finite)
    (h₁ : ∀ a ∈ A, ∃! q : V × ℕ, q.1 ∈ B ∧ R q.1 a q.2) :
    ∃ E : Set (Sym2 V × ℕ), E.ncard ≤ A.ncard ∧
      (∀ a ∈ A, ∀ v n, v ∈ B → R v a n → (s(v, a), n) ∈ E) ∧
      (∀ a ∈ A, ∃ v n, (s(v, a), n) ∈ E) ∧
      ∀ e ∈ E, ∃ v a n, v ∈ B ∧ a ∈ A ∧ R v a n ∧ e = (s(v, a), n) := by
  classical
  -- the chosen partner of `a`, with a dummy value off `A`
  let f : V → V × ℕ := fun a ↦ if ha : a ∈ A then (h₁ a ha).exists.choose else (a, 0)
  have hf : ∀ a ∈ A, (f a).1 ∈ B ∧ R (f a).1 a (f a).2 := fun a ha ↦ by
    simpa only [f, ha, ↓reduceDIte] using (h₁ a ha).exists.choose_spec
  refine ⟨(fun a ↦ (s((f a).1, a), (f a).2)) '' A, Set.ncard_image_le h₀, ?_, ?_, ?_⟩
  · -- uniqueness: any admissible partner is the chosen one
    intro a ha v n hv hR
    have : (v, n) = f a := by
      simpa only [f, ha, ↓reduceDIte] using
        (h₁ a ha).unique ⟨hv, hR⟩ (h₁ a ha).exists.choose_spec
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp this
    exact ⟨a, ha, rfl⟩
  · exact fun a ha ↦ ⟨(f a).1, (f a).2, a, ha, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨(f a).1, a, (f a).2, (hf a ha).1, ha, (hf a ha).2, rfl⟩

end Subgraph

end Construction

end TemporalGraph
