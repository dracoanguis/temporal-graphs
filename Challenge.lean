/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Sym.Sym2
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Temporal cliques admit temporal spanners of size `O(n log n)`

A *temporal clique* on a finite vertex set `V` is the complete graph on `V` in which every edge
`{u, v}` (`u ≠ v`) carries a time label `lab s(u, v) ∈ ℕ`, at which the edge can be crossed. Each
edge has exactly one label (the temporal graph is *simple*), and the labelling is *locally
injective* (*proper*): two distinct edges with a common endpoint carry distinct labels.

A *journey* is a walk whose successive edges have non-decreasing labels. A set `S` of edges
is a *temporal spanner* when every vertex can reach every other one by a journey that only uses
edges of `S`.

Casteigts, Peters and Schoeters (ICALP 2019, JCSS 2021) proved that every temporal clique on `n`
vertices admits a temporal spanner with `O(n log n)` edges. Carnevale, Casteigts and Corsini
(SAND 2025, §§2–4) give a new proof based on dismountability alone, which reduces the problem to
temporal bi-cliques and concludes with the one-sided dismountability of Angrick et al.
(ESA 2024). This file states the result, both with an explicit bound (`2 n ⌈log₂ n⌉ + 4 n`) and
in asymptotic form.

## Modelling choices

* Labels are natural numbers. Any linearly ordered set of labels on a finite clique can be
  replaced by its ranks in `ℕ` without changing which walks are journeys.
* `lab` is defined on all of `Sym2 V`; its values on the diagonal `s(v, v)` are never used,
  since a spanner contains no such pair.
* Journeys are *non-strict*: the labels are only required to be non-decreasing along the walk.
  For the cliques considered here the distinction with strict journeys (strictly increasing
  labels) disappears: each edge has one label and the labelling is locally injective, so two
  consecutive distinct edges, which share an endpoint, have distinct labels. A non-strict
  journey that is not strict must therefore cross an edge and immediately cross it back at the
  same time, a detour that can be deleted; both notions give the same reachability.
-/

@[expose] public section

namespace TemporalCliqueSpanners

variable {V : Type}

/-- The labelling `lab` of the edges of the complete graph on `V` is *locally injective*: two
distinct edges `s(u, v)` and `s(u, w)` sharing the endpoint `u` have distinct labels. -/
def IsLocallyInjective (lab : Sym2 V → ℕ) : Prop :=
  ∀ u v w : V, u ≠ v → u ≠ w → v ≠ w → lab s(u, v) ≠ lab s(u, w)

/-- `Journey S lab t u v`: there is a journey from `u` to `v` using only edges of `S`, whose
labels are non-decreasing and all at least `t`. The empty journey goes from `u` to `u`;
otherwise the journey crosses an edge `s(u, w) ∈ S` at a time `lab s(u, w) ≥ t`, then continues
from `w` no earlier than that time. -/
inductive Journey (S : Finset (Sym2 V)) (lab : Sym2 V → ℕ) : ℕ → V → V → Prop
  | nil (t : ℕ) (u : V) : Journey S lab t u u
  | cons {t : ℕ} {u w v : V} (h₀ : s(u, w) ∈ S) (h₁ : t ≤ lab s(u, w))
      (h₂ : Journey S lab (lab s(u, w)) w v) : Journey S lab t u v

/-- `S` is a *temporal spanner* of the temporal clique labelled by `lab`: `S` consists of edges of
the complete graph (no diagonal pair `s(v, v)`), and every vertex `u` reaches every vertex `v`
by a journey within `S`. -/
def IsTemporalSpanner (S : Finset (Sym2 V)) (lab : Sym2 V → ℕ) : Prop :=
  (∀ e ∈ S, ¬e.IsDiag) ∧ ∀ u v : V, Journey S lab 0 u v

/-- Explicit bound: every temporal clique on `n` vertices admits a temporal spanner with at most
`2 n ⌈log₂ n⌉ + 4 n` edges. -/
theorem exists_isTemporalSpanner_card_le (V : Type) [Finite V] (lab : Sym2 V → ℕ)
    (h : IsLocallyInjective lab) :
    ∃ S : Finset (Sym2 V), IsTemporalSpanner S lab ∧
      S.card ≤ 2 * Nat.card V * Nat.clog 2 (Nat.card V) + 4 * Nat.card V := by
  sorry

open Asymptotics Filter in
/-- Casteigts–Peters–Schoeters (ICALP 2019), reproved by Carnevale–Casteigts–Corsini (SAND 2025,
§4.1): temporal cliques on `n` vertices admit temporal spanners of size `O(n log n)`. The bound
`f` is chosen once, uniformly over all temporal cliques. -/
theorem exists_isBigO_isTemporalSpanner :
    ∃ f : ℕ → ℕ, (fun n ↦ (f n : ℝ)) =O[atTop] (fun n ↦ (n : ℝ) * Real.log n) ∧
      ∀ (V : Type) [Finite V] (lab : Sym2 V → ℕ), IsLocallyInjective lab →
        ∃ S : Finset (Sym2 V), IsTemporalSpanner S lab ∧ S.card ≤ f (Nat.card V) := by
  sorry

end TemporalCliqueSpanners
