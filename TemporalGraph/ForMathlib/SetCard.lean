/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import Mathlib.Data.Set.Card

import Mathlib.Data.Set.Finite.Lattice

/-!
# Generic lemmas about `Set.ncard`

Generic lemmas about `Set.ncard`, candidates for Mathlib. They have no graph content and live in
the `Set` namespace, ready to be upstreamed.

## Main results

* `Set.exists_median_threshold` : a median threshold for a family of times.
* `Set.finite_and_ncard_le_of_functional` : a set whose elements are each related, by a
  functional relation, to a vertex of a finite set `A` has at most `|A|` elements.
* `Set.exists_subset_ncard_halves` : split a set into two halves of complementary
  size.
* `Set.ncard_pair_le`, `Set.ncard_le_four` : an unordered
  pair (resp. four elements) has `Set.ncard` at most 2 (resp. 4).
-/

@[expose] public section

universe u

namespace Set

/-- A median threshold: for a finite set `A` and any `f : α → ℕ`, some `τ` leaves at most `|A| / 2`
elements strictly below it and at most `|A| / 2` strictly above it. Baligács 2026 cuts the
labeling ordered by the times at a source `c` at `k = ⌊n / 2⌋` (Theorem 18), which is this
threshold for `f`, the times of the edges at `c`. -/
theorem exists_median_threshold {α : Type*} {A : Set α} (f : α → ℕ) (h₀ : A.Finite) :
    ∃ τ, {v ∈ A | f v < τ}.ncard ≤ A.ncard / 2 ∧ {v ∈ A | τ < f v}.ncard ≤ A.ncard / 2 := by
  classical
  -- Proof idea: take for `τ` the first value that leaves more than `|A| / 2` elements at or below
  -- it. Then at most `|A| / 2` are strictly below (minimality), and at most `|A| / 2` are
  -- strictly above (the complement).
  rcases Nat.eq_zero_or_pos A.ncard with h₂ | h₂
  · -- `A` is empty: any threshold works
    -- both sets are subsets of `A`, of size at most `|A| = 0`
    refine ⟨0, ?_, ?_⟩ <;> exact (Set.ncard_le_ncard (Set.sep_subset _ _) h₀).trans (by omega)
  -- some threshold leaves more than `|A| / 2` elements at or below it: a bound of `f` on `A`
  have h₃ : ∃ τ, A.ncard / 2 < {v ∈ A | f v ≤ τ}.ncard := by
    obtain ⟨M, h₄⟩ := (h₀.image f).bddAbove
    have h₅ : {v ∈ A | f v ≤ M} = A := Set.sep_eq_self_iff_mem_true.2 fun v h ↦ h₄ ⟨v, h, rfl⟩
    -- `|A| / 2 < |A|` since `|A| > 0`
    refine ⟨M, ?_⟩
    rw [h₅]
    omega
  -- `τ` is the first such threshold
  refine ⟨Nat.find h₃, ?_, ?_⟩
  · -- strictly below `τ` is at or below `τ - 1`, which leaves too few elements by minimality
    rcases h₄ : Nat.find h₃ with _ | τ
    · -- `τ = 0`: nothing is strictly below
      simp only [Nat.not_lt_zero, and_false, Set.ofPred_false, Set.ncard_empty, Nat.zero_le]
    · have h₅ := Nat.find_min h₃ (h₄ ▸ Nat.lt_succ_self τ : τ < Nat.find h₃)
      simp only [Nat.lt_succ_iff]
      -- `h₅` : at most `|A| / 2` elements are at or below `τ`, by minimality
      omega
  · -- strictly above `τ` is the complement of at or below `τ`, which has more than `|A| / 2`
    have h₄ := Nat.find_spec h₃
    have h₅ : {v ∈ A | Nat.find h₃ < f v} = A \ {v ∈ A | f v ≤ Nat.find h₃} := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_and, not_le]
      exact ⟨fun ⟨hv, h⟩ ↦ ⟨hv, fun _ ↦ h⟩, fun ⟨hv, h⟩ ↦ ⟨hv, h hv⟩⟩
    rw [h₅, Set.ncard_sdiff (Set.sep_subset _ _) (h₀.subset (Set.sep_subset _ _))]
    -- `|A| - |B| ≤ |A| / 2` since `|B| > |A| / 2`
    omega

variable {V : Type u} {A : Set V}

/-- A set `S` in which each element is related by a functional relation `R` to a vertex of a
finite set `A` is finite, with at most `|A|` elements: at most one element per vertex. -/
theorem finite_and_ncard_le_of_functional {α : Type*} {S : Set α} (R : V → α → Prop)
    (h₀ : A.Finite) (h₁ : ∀ e ∈ S, ∃ v ∈ A, R v e) (h₂ : ∀ v e e', R v e → R v e' → e = e') :
    S.Finite ∧ S.ncard ≤ A.ncard := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
  · simp
  obtain ⟨v₀, -⟩ := h₁ e₀ he₀
  have : Nonempty V := ⟨v₀⟩ -- needed by `choose!`
  -- choose a related vertex of `A` for each element of `S`; this is an injection
  choose! f hfA hfR using h₁
  have h₃ : S.InjOn f := fun e he e' he' h ↦ h₂ (f e) e e' (hfR e he) (h ▸ hfR e' he')
  exact ⟨Set.Finite.of_injOn hfA h₃ h₀, Set.ncard_le_ncard_of_injOn f hfA h₃ h₀⟩

/-- Split a set into two halves of complementary size, `⌈|s| / 2⌉` and `⌊|s| / 2⌋`: used to divide
a bi-clique's source part in two before recursing (SAND 2025, §4.1, split step). Holds
unconditionally, including when `s` is infinite (both sides are then `0`, since `s.ncard = 0`). -/
lemma exists_subset_ncard_halves {α : Type*} (s : Set α) :
    ∃ s₁ ⊆ s, s₁.ncard = (s.ncard + 1) / 2 ∧ (s \ s₁).ncard = s.ncard / 2 := by
  rcases s.finite_or_infinite with hfin | hinf
  · obtain ⟨s₁, hsub, hcard⟩ :=
      Set.exists_subset_card_eq (s := s) (n := (s.ncard + 1) / 2) (by omega)
    refine ⟨s₁, hsub, hcard, ?_⟩
    rw [Set.ncard_sdiff hsub (hfin.subset hsub), hcard]
    omega
  · have h0 : s.ncard = 0 := hinf.ncard
    exact ⟨∅, Set.empty_subset s, by simp [h0], by simp [h0]⟩

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

end Set

/-! ### Deprecated aliases -/

@[deprecated (since := "2026-10-29")]
alias TemporalGraph.exists_threshold := Set.exists_median_threshold

@[deprecated (since := "2026-10-29")]
alias TemporalGraph.finite_and_ncard_le_of_functional := Set.finite_and_ncard_le_of_functional

@[deprecated (since := "2026-10-29")]
alias TemporalGraph.Subgraph.exists_ncard_halves := Set.exists_subset_ncard_halves

@[deprecated (since := "2026-10-29")]
alias TemporalGraph.Subgraph.ncard_pair_le := Set.ncard_pair_le

@[deprecated (since := "2026-10-29")]
alias TemporalGraph.Subgraph.ncard_le_four := Set.ncard_le_four
