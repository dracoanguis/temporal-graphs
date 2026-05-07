/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic


namespace LooplessTemporalGraph


variable {V W X : Type*}

section Map

protected def map (f : V ↪ W) (G : LooplessTemporalGraph V) : LooplessTemporalGraph W where
  Adj x y t := Relation.Map (fun a b ↦ G.Adj a b t) f f x y
  symm t a b := by
    rintro ⟨v, w, h, _⟩
    aesop (add norm unfold Relation.Map) (add forward safe Adj.symm)
  loopless t := ⟨fun v ↦ by aesop (add norm unfold Relation.Map)⟩

@[simp]
theorem map_adj (f : V ↪ W) (G : LooplessTemporalGraph V) (u w : W) (t : ℕ)
: (G.map f).Adj u w t ↔ ∃ u' w' : V, G.Adj u' w' t ∧ f u' = u ∧ f w' = w
:= Iff.rfl

lemma map_adj_apply {G : LooplessTemporalGraph V} {f : V ↪ W} {a b : V} {t : ℕ}
: (G.map f).Adj (f a) (f b) t ↔ G.Adj a b t
:= by simp

end Map

section Comap

protected def comap (f : V → W) (G : LooplessTemporalGraph W) : LooplessTemporalGraph V where
  Adj u v t := G.Adj (f u) (f v) t
  symm t _ _ h := G.symm t h
  loopless _ := ⟨fun v ↦ by simp⟩

@[simp] lemma comap_adj {G : LooplessTemporalGraph W} {f : V → W} {u v : V} {t : ℕ}
: (G.comap f).Adj u v t ↔ G.Adj (f u) (f v) t
:= Iff.rfl

end Comap

section Induce

abbrev induce (s : Set V) (G : LooplessTemporalGraph V) : LooplessTemporalGraph s :=
  G.comap (Function.Embedding.subtype _)

lemma induce_adj {G : LooplessTemporalGraph V} {s : Set V} {u v : s} {t : ℕ}
: (G.induce s).Adj u v t ↔ G.Adj u v t
:= .rfl

end Induce

section Hom

variable (G : LooplessTemporalGraph V) (G' : LooplessTemporalGraph W) {t : ℕ}

abbrev Hom := RelHom (fun x y ↦ G.Adj x y t) (fun x y ↦ G'.Adj x y t)

abbrev Embedding := RelEmbedding (fun x y ↦ G.Adj x y t) (fun x y ↦ G'.Adj x y t)

@[inherit_doc] infixl:50 " →g " => Hom
@[inherit_doc] infixl:50 " ↪g " => Embedding

end Hom

section Iso

/-- An isomorphism on a SimpleTemporalGrpah use the `≃tg` notation.
It is defined as an Isomorphism on each adjacency rel at everytime. -/
structure Iso (G : LooplessTemporalGraph V) (G' : LooplessTemporalGraph W) where
  toIso : ∀ t, RelIso (fun x y ↦ G.Adj x y t) (fun x y ↦ G'.Adj x y t)

@[inherit_doc] infixl:50 " ≃tg " => Iso

variable (G : LooplessTemporalGraph V) (G' : LooplessTemporalGraph W)

-- def Iso.toEquiv (Φ : G ≃tg G') : V ≃ W :=
--   Φ.toIso 0   -- all times give the same bijection

def Iso.toEquiv (Φ : G ≃tg G') : V ≃ W :=
  Φ.toIso 0 |>.toEquiv

-- lemma Iso.eq_time_bijection (Φ : G ≃tg G') (t₁ t₂ : ℕ)
-- : (Φ.toIso t₁).toEquiv = (Φ.toIso t₂).toEquiv
-- := by sorry

-- theorem tempIso_iff_per_time_iso
-- : (G ≃tg G') ↔ ∀ t, RelIso (fun x y ↦ G.Adj x y t) (fun x y ↦ G'.Adj x y t)
-- := sorry

/-- The identity isomorphism of a graph with itself. -/
abbrev refl : G ≃tg G :=
  ⟨fun _ : ℕ ↦RelIso.refl _⟩

end Iso

end LooplessTemporalGraph
