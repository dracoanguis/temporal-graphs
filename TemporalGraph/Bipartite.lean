/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Subgraph
import TemporalGraph.Connectivity.Basic

/-!
# Bipartite temporal graphs

This module defines bipartite temporal graphs and temporal bi-cliques, mirroring Mathlib's
`SimpleGraph.IsBipartiteWith` (`Mathlib/Combinatorics/SimpleGraph/Bipartite.lean`). As with the
rest of the library, no symmetry is assumed unless a result genuinely needs it: `IsBipartiteWith`,
`between` and `IsBicliqueWith` themselves place no `[IsSymm]` instance on `G`, which also covers
the oriented case that Mathlib's static API does not address. The partition `s`/`t` is data, so it
is always an explicit argument, never bundled into a type class as `IsSymm`/`IsLoopless` are.

Temporal bi-cliques (`IsBicliqueWith`) are the object at stake in Carnevale–Casteigts–Corsini's
reduction of temporal cliques to bi-cliques (SAND 2025, §1.1 and Corollary 4.1): a clique restricted
to the edges crossing a disjoint partition (`between`) is exactly a bi-clique on that partition
(`IsClique.between_isBicliqueWith`). This file develops the definitions, their basic API, the
bridge to Mathlib's static bipartite graphs (`isBipartite_iff_simpleFootprint`), and a labelled
complete bipartite graph constructor (`completeBipartite`); the reduction itself (SAND 2025,
Corollary 4.1) is left to a future development.

## Main definitions

* `TemporalGraph.IsBipartiteWith`, `TemporalGraph.IsBipartite` : a temporal graph bipartite with
  given parts, resp. admitting some bipartition.
* `TemporalGraph.between` : the restriction of a temporal graph to the arcs crossing a partition.
* `TemporalGraph.IsBicliqueWith`, `TemporalGraph.IsBiclique` : temporal bi-cliques (SAND 2025,
  §1.1).
* `TemporalGraph.completeBipartite` : the labelled complete bipartite graph on `α ⊕ β`.
* `TemporalGraph.Subgraph.between` : the subgraph-level counterpart of `between`.

`IsBiclique`, like `IsClique`, takes the vertex set `S` it quantifies over as an explicit
argument (Mathlib's convention), so it needs no `Subgraph`-level duplicate: `H.IsBiclique
H.verts` resolves through the inherited `TemporalGraph.IsBiclique`, just as `H.IsClique H.verts`
does.

## Main results

* `TemporalGraph.isBipartiteWith_iff_simpleFootprint`,
  `TemporalGraph.isBipartite_iff_simpleFootprint` : the bridge with Mathlib's
  `SimpleGraph.IsBipartiteWith`/`IsBipartite`, obtained through `simpleFootprint`.
* `TemporalGraph.IsClique.between_isBicliqueWith` : restricting a clique to the arcs between two
  disjoint parts gives a temporal bi-clique on those parts (the one-step link used by SAND 2025,
  Corollary 4.1).
* `TemporalGraph.Subgraph.reachable_of_isBicliqueWith` : in a bi-clique on `s`/`t`, every vertex of
  `s` reaches every vertex of `t`.
* `TemporalGraph.Subgraph.isBicliqueWith_induce`,
  `TemporalGraph.Subgraph.isBicliqueWith_deleteVerts` : restricting a bi-clique to `s' ∪ t` (for
  `s' ⊆ s`), resp. deleting vertices from it, keeps a bi-clique on the corresponding parts
  (SAND 2025, §4.1, feeding into one-sided dismountability).

## References

* Carnevale, Casteigts & Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025
  (LIPIcs 330, doi:10.4230/LIPIcs.SAND.2025.6, arXiv:2502.01321), §1.1 — temporal bi-cliques.
* Mathlib's `SimpleGraph.IsBipartiteWith`, `SimpleGraph.between` and
  `SimpleGraph.completeBipartiteGraph` (`Mathlib/Combinatorics/SimpleGraph/Bipartite.lean`) — the
  static model this file mirrors.
-/

universe u

namespace TemporalGraph

variable {V : Type u}

section IsBipartiteWith

variable {G H : TemporalGraph V} {s t : Set V} {v w : V} {n : ℕ}

/-- `G` is bipartite with parts `s` and `t`: the parts are disjoint and every arc, at every time,
goes from one part to the other. As in Mathlib's `SimpleGraph.IsBipartiteWith`, `s ∪ t` need only
cover the vertices that carry an arc. No symmetry is assumed, so this also covers oriented
graphs. -/
structure IsBipartiteWith (G : TemporalGraph V) (s t : Set V) : Prop where
  disjoint : Disjoint s t
  mem_of_adj ⦃v w : V⦄ ⦃n : ℕ⦄ :
    G.Adj v w n → v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s

/-- `G` admits a bipartition. There is no temporal `Colorable`, so this is the existential form;
`isBipartite_iff_simpleFootprint` identifies it with Mathlib's `Colorable 2` definition. -/
def IsBipartite (G : TemporalGraph V) : Prop := ∃ s t : Set V, G.IsBipartiteWith s t

/-- Swapping the two parts of a bipartition is still a bipartition. -/
theorem IsBipartiteWith.symm (h : G.IsBipartiteWith s t) : G.IsBipartiteWith t s where
  disjoint := h.disjoint.symm
  mem_of_adj _ _ _ hadj := (h.mem_of_adj hadj).symm

/-- The iff form of `IsBipartiteWith.symm`: `G` is bipartite with parts `s`/`t` iff with `t`/`s`. -/
theorem isBipartiteWith_comm : G.IsBipartiteWith s t ↔ G.IsBipartiteWith t s :=
  ⟨IsBipartiteWith.symm, IsBipartiteWith.symm⟩

/-- If `v ∈ s` and `v` is adjacent to `w`, then `w ∈ t`. -/
theorem IsBipartiteWith.mem_of_mem_adj (h : G.IsBipartiteWith s t) (hv : v ∈ s)
    (hadj : G.Adj v w n) : w ∈ t := by
  have hor := h.mem_of_adj hadj
  have hnv : v ∉ t := Set.disjoint_left.mp h.disjoint hv
  tauto

/-- If `v ∈ t` and `v` is adjacent to `w`, then `w ∈ s`. -/
theorem IsBipartiteWith.mem_of_mem_adj' (h : G.IsBipartiteWith s t) (hv : v ∈ t)
    (hadj : G.Adj v w n) : w ∈ s := by
  have hor := h.mem_of_adj hadj
  have hnv : v ∉ s := Set.disjoint_right.mp h.disjoint hv
  tauto

/-- A bipartition is inherited by any spanning subgraph: fewer adjacencies can only make the
condition easier to satisfy. -/
theorem IsBipartiteWith.mono (h : H.IsBipartiteWith s t) (hle : G ≤ H) :
    G.IsBipartiteWith s t where
  disjoint := h.disjoint
  mem_of_adj _ _ _ hadj := h.mem_of_adj (hle hadj)

/-- A bipartition rules out loops: a loop at `v` would put `v` in both parts, contradicting their
disjointness. -/
theorem IsBipartiteWith.isLoopless (h : G.IsBipartiteWith s t) : G.IsLoopless :=
  ⟨fun _ ↦ ⟨fun v hv ↦ by
    rcases h.mem_of_adj hv with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact Set.disjoint_left.mp h.disjoint hs ht
    · exact Set.disjoint_left.mp h.disjoint ht hs⟩⟩

/-- `⊥` is bipartite with any pair of disjoint parts: there is no arc to check. -/
theorem isBipartiteWith_bot : (⊥ : TemporalGraph V).IsBipartiteWith s t ↔ Disjoint s t :=
  ⟨fun h ↦ h.disjoint, fun h ↦ ⟨h, fun _ _ _ hadj ↦ hadj.elim⟩⟩

/-- A bipartition witnesses that `G` is bipartite. -/
theorem IsBipartiteWith.isBipartite (h : G.IsBipartiteWith s t) : G.IsBipartite := ⟨s, t, h⟩

end IsBipartiteWith

section SimpleFootprintBridge

variable {G : TemporalGraph V} {s t : Set V}

/-- The bridge to Mathlib's static bipartite graphs: `G.IsBipartiteWith s t` is exactly
`(G.simpleFootprint hs hl).IsBipartiteWith s t`, since both discard the time labels and keep only
the underlying adjacency. -/
theorem isBipartiteWith_iff_simpleFootprint (hs : G.IsSymm) (hl : G.IsLoopless) :
    G.IsBipartiteWith s t ↔ (G.simpleFootprint hs hl).IsBipartiteWith s t :=
  ⟨fun h ↦ ⟨h.disjoint, fun _ _ ⟨_, hadj⟩ ↦ h.mem_of_adj hadj⟩,
    fun h ↦ ⟨h.disjoint, fun _ _ n hadj ↦ h.mem_of_adj ⟨n, hadj⟩⟩⟩

/-- The bridge to Mathlib's `IsBipartite = Colorable 2`, through
`isBipartiteWith_iff_simpleFootprint` and Mathlib's
`SimpleGraph.isBipartite_iff_exists_isBipartiteWith`. -/
theorem isBipartite_iff_simpleFootprint (hs : G.IsSymm) (hl : G.IsLoopless) :
    G.IsBipartite ↔ (G.simpleFootprint hs hl).IsBipartite := by
  rw [IsBipartite, SimpleGraph.isBipartite_iff_exists_isBipartiteWith]
  exact exists_congr fun s ↦ exists_congr fun t ↦ isBipartiteWith_iff_simpleFootprint hs hl

end SimpleFootprintBridge

section Between

variable {G : TemporalGraph V} {s t : Set V} {v w : V} {n : ℕ}

/-- The arcs of `G` that cross between `s` and `t` (Mathlib's `SimpleGraph.between`). -/
def between (s t : Set V) (G : TemporalGraph V) : TemporalGraph V where
  Adj v w n := G.Adj v w n ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s)

/-- Unfolding lemma for `between`: an arc of `G.between s t` is an arc of `G` crossing between `s`
and `t`. -/
@[simp, grind =]
theorem between_adj :
    (G.between s t).Adj v w n ↔ G.Adj v w n ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s) :=
  Iff.rfl

/-- `G.between s t` is a subgraph of `G`: restricting to the crossing arcs only removes arcs. -/
theorem between_le : G.between s t ≤ G := fun h ↦ h.1

/-- `between` is symmetric in its two parts. -/
theorem between_comm : G.between s t = G.between t s := by ext; grind only [= between_adj]

/-- `G.between s t` is bipartite with parts `s` and `t` when they are disjoint. -/
theorem between_isBipartiteWith (h : Disjoint s t) : (G.between s t).IsBipartiteWith s t where
  disjoint := h
  mem_of_adj _ _ _ hadj := hadj.2

instance between_isSymm [G.IsSymm] : (G.between s t).IsSymm :=
  IsSymm.of_adj fun _ _ _ h ↦ by
    obtain ⟨hadj, hor⟩ := h
    exact ⟨hadj.symm, by tauto⟩

instance between_isLoopless [G.IsLoopless] : (G.between s t).IsLoopless :=
  ⟨fun _ ↦ ⟨fun _ h ↦ G.irrefl h.1⟩⟩

/-- Restricting to the arcs between two parts keeps simplicity: at most one time per ordered
pair. -/
theorem IsSimple.between (h : G.IsSimple) (s t : Set V) : (G.between s t).IsSimple :=
  h.mono between_le

/-- Restricting to the arcs between two parts keeps properness: at most one destination per
source and time. -/
theorem IsProper.between (h : G.IsProper) (s t : Set V) : (G.between s t).IsProper :=
  fun x y z n hyz ↦ h x y z n ⟨hyz.1.1, hyz.2.1⟩

end Between

section IsBicliqueWith

variable {G : TemporalGraph V} {S s t : Set V} {v w : V}

/-- `G` is a temporal bi-clique on parts `s` and `t` (SAND 2025, §1.1): it is bipartite with these
parts, and every vertex of `s` has an arc, at some time, to every vertex of `t`. Two fields rather
than `extends`, per the library's convention. -/
structure IsBicliqueWith (G : TemporalGraph V) (s t : Set V) : Prop where
  isBipartiteWith : G.IsBipartiteWith s t
  adj_of_mem ⦃v w : V⦄ : v ∈ s → w ∈ t → ∃ n, G.Adj v w n

/-- `G` is a temporal bi-clique on the vertex set `S`: `S` splits into two parts covering it, with
a bi-clique between them (covering matters here, unlike for `IsBipartite`, since an extra vertex
must still see the other part). `G.IsBiclique Set.univ` is a bi-clique graph. -/
def IsBiclique (G : TemporalGraph V) (S : Set V) : Prop :=
  ∃ s t : Set V, s ∪ t = S ∧ G.IsBicliqueWith s t

/-- The reverse-oriented arc from `w ∈ t` to `v ∈ s`, using symmetry directly rather than
rebuilding the whole swapped bi-clique (compare `IsBicliqueWith.symm`). -/
theorem IsBicliqueWith.adj_of_mem' [G.IsSymm] (h : G.IsBicliqueWith s t) (hv : v ∈ s)
    (hw : w ∈ t) : ∃ n, G.Adj w v n := by
  obtain ⟨n, hadj⟩ := h.adj_of_mem hv hw
  exact ⟨n, hadj.symm⟩

/-- Swapping the two parts of a bi-clique needs symmetry, to reverse the direction of each arc. -/
theorem IsBicliqueWith.symm [G.IsSymm] (h : G.IsBicliqueWith s t) : G.IsBicliqueWith t s where
  isBipartiteWith := h.isBipartiteWith.symm
  adj_of_mem _ _ hv hw := h.adj_of_mem' hw hv

/-- Restricting a clique to the arcs between two disjoint parts gives a temporal bi-clique on
these parts (SAND 2025, the one-step link used by Corollary 4.1). -/
theorem IsClique.between_isBicliqueWith (hc : G.IsClique S) (hs : s ⊆ S) (ht : t ⊆ S)
    (h : Disjoint s t) : (G.between s t).IsBicliqueWith s t where
  isBipartiteWith := between_isBipartiteWith h
  adj_of_mem v w hv hw := by
    have hvw : v ≠ w := by rintro rfl; exact Set.disjoint_left.mp h hv hw
    obtain ⟨n, hadj⟩ := hc (hs hv) (ht hw) hvw
    exact ⟨n, hadj, Or.inl ⟨hv, hw⟩⟩

end IsBicliqueWith

section CompleteBipartite

variable {α β : Type u}

/-- The temporal complete bipartite graph on `α ⊕ β` whose edge `{a, b}` exists at time `f a b`
only (analogue of Mathlib's `completeBipartiteGraph`, with a labelling). -/
def completeBipartite (f : α → β → ℕ) : TemporalGraph (α ⊕ β) where
  Adj
    | .inl a, .inr b, n => f a b = n
    | .inr b, .inl a, n => f a b = n
    | _, _, _ => False

/-- An arc from the left summand to the right exists at time `f a b` only. -/
@[simp, grind =]
theorem completeBipartite_adj_inl_inr {f : α → β → ℕ} {a : α} {b : β} {n : ℕ} :
    (completeBipartite f).Adj (.inl a) (.inr b) n ↔ f a b = n :=
  Iff.rfl

/-- An arc from the right summand to the left exists at time `f a b` only (the reverse
orientation of `completeBipartite_adj_inl_inr`). -/
@[simp, grind =]
theorem completeBipartite_adj_inr_inl {f : α → β → ℕ} {a : α} {b : β} {n : ℕ} :
    (completeBipartite f).Adj (.inr b) (.inl a) n ↔ f a b = n :=
  Iff.rfl

/-- There is no arc between two vertices of the left summand. -/
@[simp, grind .]
theorem completeBipartite_adj_inl_inl {f : α → β → ℕ} {a a' : α} {n : ℕ} :
    ¬(completeBipartite f).Adj (.inl a) (.inl a') n :=
  id

/-- There is no arc between two vertices of the right summand. -/
@[simp, grind .]
theorem completeBipartite_adj_inr_inr {f : α → β → ℕ} {b b' : β} {n : ℕ} :
    ¬(completeBipartite f).Adj (.inr b) (.inr b') n :=
  id

instance completeBipartite_isSymm (f : α → β → ℕ) : (completeBipartite f).IsSymm :=
  IsSymm.of_adj fun n x y h ↦ by
    match x, y with
    | .inl _, .inr _ => exact h
    | .inr _, .inl _ => exact h
    | .inl _, .inl _ => exact h.elim
    | .inr _, .inr _ => exact h.elim

instance completeBipartite_isLoopless (f : α → β → ℕ) : (completeBipartite f).IsLoopless :=
  ⟨fun _ ↦ ⟨fun x h ↦ by
    match x with
    | .inl _ => exact h.elim
    | .inr _ => exact h.elim⟩⟩

/-- `completeBipartite f` is a temporal bi-clique on the two summands. -/
theorem completeBipartite_isBicliqueWith (f : α → β → ℕ) :
    (completeBipartite f).IsBicliqueWith
      (Set.range (Sum.inl : α → α ⊕ β)) (Set.range (Sum.inr : β → α ⊕ β)) where
  isBipartiteWith :=
    { disjoint := by
        rw [Set.disjoint_left]
        rintro x ⟨a, rfl⟩ ⟨b, hb⟩
        exact absurd hb (by simp)
      mem_of_adj := by
        intro x y n h
        match x, y with
        | .inl a, .inr b => exact Or.inl ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
        | .inr b, .inl a => exact Or.inr ⟨⟨b, rfl⟩, ⟨a, rfl⟩⟩
        | .inl _, .inl _ => exact h.elim
        | .inr _, .inr _ => exact h.elim }
  adj_of_mem v w hv hw := by
    obtain ⟨a, rfl⟩ := hv
    obtain ⟨b, rfl⟩ := hw
    exact ⟨f a b, rfl⟩

/-- `completeBipartite f` is a temporal bi-clique, covering the whole vertex type. -/
theorem completeBipartite_isBiclique (f : α → β → ℕ) :
    (completeBipartite f).IsBiclique Set.univ :=
  ⟨_, _, by
    ext x
    cases x <;> simp, completeBipartite_isBicliqueWith f⟩

/-- `completeBipartite f` is simple: at most one time per ordered pair. -/
theorem completeBipartite_isSimple (f : α → β → ℕ) : (completeBipartite f).IsSimple := by
  grind

/-- `completeBipartite f` is proper when `f` is injective in each argument separately. -/
theorem completeBipartite_isProper {f : α → β → ℕ} (h₁ : ∀ a, (f a).Injective)
    (h₂ : ∀ b, (f · b).Injective) : (completeBipartite f).IsProper := by
  intro x y z n h
  match x, y, z, h with
  | .inl a, .inr b, .inr b', ⟨h1, h2⟩ =>
    have h1' : f a b = n := h1
    have h2' : f a b' = n := h2
    exact congrArg Sum.inr (h₁ a (h1'.trans h2'.symm))
  | .inr b, .inl a, .inl a', ⟨h1, h2⟩ =>
    have h1' : f a b = n := h1
    have h2' : f a' b = n := h2
    exact congrArg Sum.inl (h₂ b (h1'.trans h2'.symm))
  | .inl _, .inl _, _, ⟨h1, _⟩ => exact h1.elim
  | .inr _, .inr _, _, ⟨h1, _⟩ => exact h1.elim
  | .inl _, .inr _, .inl _, ⟨_, h2⟩ => exact h2.elim
  | .inr _, .inl _, .inr _, ⟨_, h2⟩ => exact h2.elim

end CompleteBipartite

section Subgraph

variable {G : TemporalGraph V} {H : Subgraph G} {s t : Set V}

/-- The subgraph of `H` restricted to the arcs crossing between `s` and `t` — the spanning
restriction used by SAND 2025 when restricting the ambient graph to the edges between `V⁻` and
`V⁺`. Follows the `induce` pattern (`Subgraph.induce`). -/
def Subgraph.between (H : Subgraph G) (s t : Set V) : Subgraph G where
  verts := H.verts
  Adj v w n := H.Adj v w n ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s)
  adj_sub h := H.adj_sub h.1
  edge_vert h := H.edge_vert h.1
  edge_vert' h := H.edge_vert' h.1

/-- Unfolding lemma for `Subgraph.between`: an arc of `H.between s t` is an arc of `H` crossing
between `s` and `t`. -/
@[simp, grind =]
theorem Subgraph.between_adj {v w : V} {n : ℕ} :
    (H.between s t).Adj v w n ↔ H.Adj v w n ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s) :=
  Iff.rfl

/-- `Subgraph.between` keeps the same vertex set as `H`: it only restricts the arcs. -/
@[simp, grind =]
theorem Subgraph.between_verts : (H.between s t).verts = H.verts :=
  rfl

/-- `H.between s t` is a subgraph of `H`. -/
theorem Subgraph.between_le : H.between s t ≤ H :=
  ⟨subset_rfl, fun hadj ↦ hadj.1⟩

/-- `Subgraph.between` commutes with `toTemporalGraph`: the subgraph-level restriction matches the
ambient `TemporalGraph.between`. -/
theorem Subgraph.toTemporalGraph_between :
    (H.between s t).toTemporalGraph = H.toTemporalGraph.between s t :=
  rfl

instance Subgraph.between_isSymm [H.IsSymm] : (H.between s t).IsSymm :=
  IsSymm.of_adj fun _ _ _ h ↦ by
    obtain ⟨hadj, hor⟩ := h
    exact ⟨TemporalGraph.adj_symm hadj, by tauto⟩

/-- In a bi-clique on `s` and `t`, every vertex of `s` reaches every vertex of `t`, by the edge
joining them. -/
lemma Subgraph.reachable_of_isBicliqueWith {s t : Set V} {x y : V}
    (h₀ : H.IsBicliqueWith s t) (h₁ : x ∈ s) (h₂ : y ∈ t) :
    H.Reachable x y := by
  obtain ⟨n, hn⟩ := h₀.adj_of_mem h₁ h₂
  exact reachable_of_nonempty_NonemptyTemporalWalk ⟨n, n, ⟨.Single hn⟩⟩

/-- Restricting a bi-clique on `s` and `t` to `s' ∪ t`, for `s' ⊆ s`, gives a bi-clique on `s'` and
`t`: the subproblem of SAND 2025, §4.1. -/
lemma Subgraph.isBicliqueWith_induce {s t s' : Set V}
    (h₀ : H.IsBicliqueWith s t) (h₁ : s' ⊆ s) :
    (H.induce (s' ∪ t)).IsBicliqueWith s' t where
  isBipartiteWith :=
    { disjoint := h₀.isBipartiteWith.disjoint.mono_left h₁
      mem_of_adj := by
        rintro v w n ⟨hv, hw, hadj⟩
        have hdis := h₀.isBipartiteWith.disjoint
        rcases h₀.isBipartiteWith.mem_of_adj hadj with ⟨hvs, hwt⟩ | ⟨hvt, hws⟩
        · exact Or.inl ⟨hv.resolve_right (Set.disjoint_left.mp hdis hvs), hwt⟩
        · exact Or.inr ⟨hvt, hw.resolve_right (Set.disjoint_left.mp hdis hws)⟩ }
  adj_of_mem v w hv hw := by
    obtain ⟨n, hn⟩ := h₀.adj_of_mem (h₁ hv) hw
    exact ⟨n, Or.inl hv, Or.inr hw, hn⟩

/-- Deleting vertices from a temporal bi-clique keeps a bi-clique, on the two parts with those
vertices removed (SAND 2025, §4.1, the `deleteVerts` counterpart of `isBicliqueWith_induce`). -/
lemma Subgraph.isBicliqueWith_deleteVerts {s t u : Set V} (h₀ : H.IsBicliqueWith s t) :
    (H.deleteVerts u).IsBicliqueWith (s \ u) (t \ u) where
  isBipartiteWith :=
    { disjoint := Disjoint.mono Set.sdiff_subset Set.sdiff_subset h₀.isBipartiteWith.disjoint
      mem_of_adj := by
        rintro v w n ⟨hv, hw, hadj⟩
        rcases h₀.isBipartiteWith.mem_of_adj hadj with ⟨hvs, hwt⟩ | ⟨hvt, hws⟩
        · exact Or.inl ⟨⟨hvs, hv.2⟩, ⟨hwt, hw.2⟩⟩
        · exact Or.inr ⟨⟨hvt, hv.2⟩, ⟨hws, hw.2⟩⟩ }
  adj_of_mem v w hv hw := by
    obtain ⟨n, hadj⟩ := h₀.adj_of_mem hv.1 hw.1
    exact ⟨n, ⟨H.edge_vert hadj, hv.2⟩, ⟨H.edge_vert' hadj, hw.2⟩, hadj⟩

end Subgraph

end TemporalGraph
