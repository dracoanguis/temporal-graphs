/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.LinearSpanner.ExtendedStar
public import TemporalGraph.LinearSpanner.Reduction
public import TemporalGraph.LinearSpanner.SimpleStar

import TemporalGraph.Helpers.SetCard

/-!
# Linear spanners of temporal bi-cliques

Baligács 2026, §4 and Theorem 3. This module concludes the proof that a temporal bi-clique has a
spanner with a linear number of edges, in the library's subgraph-level, one-sided formulation
(`Subgraph.IsSpannerFromTo`).

Vocabulary (see `LinearSpanner/Stars.lean`). For a source `c` and a threshold time `τ`, a source
`v` is *early* when `λ(c, N_min v) ≤ τ` and *upper* when `τ < λ(c, N_min v)`; a target `u` is *late*
when `τ ≤ λ(c, u)`. An upper source is a *3-hop crossing* when it is `3`-hop-`τ`-cut-crossing
(`IsCutCrossing`): a temporal walk of at most `4` edges leads from it to an early source's `N_min`,
and ends with the edge of that vertex to `c`.

* Lemma 17 cuts the labeling of an extremally matched bi-clique, ordered by the times at a source
  `c`, at a threshold `τ`. At most `6n` edges then make every source reach the late targets, or
  make the early sources reach every target. Either every upper source is a 3-hop crossing
  (Observation 9, plus `E_max`), or a non-crossing one, `v`, makes `Ext(c) ∪ Ext(N_min v)` work
  (Lemma 16).
* Theorem 18 (with Theorem 6) recurses on what is left uncovered, at the median threshold: the
  *uncovered part* is the set of the pairs (source, target) not reached by the `≤ 6n` edges of
  Lemma 17, namely the pairs of upper sources and targets, or of sources and non-late targets. It
  is a bi-clique with one side of size at most `n / 2`, which Lemma 5 reduces again to an
  extremally matched one. The recurrence `f(n) ≤ 9n - 4x + f(x)`, `x ≤ n / 2`, gives
  `f(n) ≤ 14n`. The spanner obtained contains `E_min ∪ E_max`, so it is temporally connected.
* Theorem 3 combines Lemma 5 and Theorem 18 for an arbitrary finite simple proper bi-clique.

Compare with `Subgraph.exists_isSpannerFromTo_ncard_le`, the `O(n log n)` bound of SAND 2025,
§4.1.

## Main results

* `TemporalGraph.IsExtremallyMatched.exists_reachable_of_threshold` : Baligács 2026, Lemma 17.
* `TemporalGraph.IsExtremallyMatched.exists_isSpannerFromTo_temporallyConnected` : Baligács 2026,
  Theorem 18 (with Theorem 6), a temporally connected one-sided spanner with at most `14 |s|` edges.
* `TemporalGraph.Subgraph.exists_isSpannerFromTo_ncard_le_linear` : Baligács 2026, Theorem 3.

## References

* Júlia Baligács, *Temporal Cliques Admit Linear Spanners*, arXiv:2606.05156v1 (2026), §4 and
  Theorem 3.
-/

@[expose] public section

universe u

namespace TemporalGraph

variable {V : Type u} {G : TemporalGraph V} {s t : Set V}

namespace IsExtremallyMatched

variable {H : Subgraph G} [Finite H.verts] [H.IsSymm] {c : V}

section Cut

/-- Baligács 2026, Lemma 17: cut the labeling of an extremally matched bi-clique `H`, ordered by
the times at a source `c`, at a threshold time `τ`. Some set `E` of at most `6 |s|` edges of `H`,
containing `E_min ∪ E_max`, makes either every source reach every late target
(`H.lateTargets t c τ`, `τ ≤ λ(c, u)`), or every early source (`H.earlySources s c τ`,
`λ(c, N_min v) ≤ τ`) reach every target. (The cut `τ` is arbitrary here; the paper's
`k = ⌊n / 2⌋` is chosen in Theorem 18.)

Proof idea: if every upper source is a 3-hop crossing, Observation 9 with `m = 3`, plus `E_max`,
gives the first case; otherwise a non-crossing upper source `v` gives the second, by Lemma 16, with
`Ext(c) ∪ Ext(N_min v)`. -/
theorem exists_reachable_of_threshold (h : H.IsExtremallyMatched s t) (h₀ : H.IsSimple)
    (h₁ : H.IsProper) (h₂ : c ∈ s) (τ : ℕ) :
    ∃ E ⊆ H.edgeSet, E.ncard ≤ 6 * s.ncard ∧ H.eMin s ∪ H.eMax s ⊆ E ∧
      ((∀ x ∈ s, ∀ y ∈ H.lateTargets t c τ,
          (Subgraph.fromEdgeSet G E).Reachable x y) ∨
        (∀ x ∈ H.earlySources s c τ, ∀ y ∈ t,
          (Subgraph.fromEdgeSet G E).Reachable x y)) := by
  by_cases hcross : ∀ v ∈ s, (∃ u ∈ H.earliestNeighborFn v, ∃ k, H.Adj c u k ∧ τ < k) →
      H.IsCutCrossing s c τ 3 v
  · -- (i) every upper source is a 3-hop crossing: Observation 9, then `Star(c)` and `E_max`
    obtain ⟨E, hEH, hEcard, hEreach⟩ := h.exists_reachable_simpleStar h₀ h₁ c τ 3
    refine ⟨E ∪ H.simpleStar s t c ∪ H.eMax s, ?_, ?_, ?_, Or.inl ?_⟩
    · exact Set.union_subset (Set.union_subset hEH simpleStar_subset_edgeSet)
        eMax_subset_edgeSet
    · -- `|E| ≤ 3n`, `|Star(c)| ≤ |E_min| + |inc c| ≤ 2n` and `|E_max| ≤ n`, with `|t| = |s| = n`
      have h₃ : E.ncard ≤ 3 * s.ncard :=
        hEcard.trans (Nat.mul_le_mul_left 3 (Set.ncard_le_ncard (Set.sep_subset _ _) h.finite_left))
      have h₄ : (H.simpleStar s t c).ncard ≤ s.ncard + t.ncard :=
        (Set.ncard_union_le _ _).trans (Nat.add_le_add (ncard_eMin_le h₀ h.finite_left)
          (ncard_incidentEdges_le h₀ h.finite_right))
      have h₅ := ncard_eMax_le (A := s) h₀ h.finite_left
      have h₆ := h.ncard_eq h₁
      calc (E ∪ H.simpleStar s t c ∪ H.eMax s).ncard
          ≤ E.ncard + (H.simpleStar s t c).ncard + (H.eMax s).ncard :=
            (Set.ncard_union_le _ _).trans (Nat.add_le_add_right (Set.ncard_union_le _ _) _)
        -- `3 |s| + (|s| + |t|) + |s| = 6 |s|`, as `|t| = |s|`
        _ ≤ 6 * s.ncard := by omega
    · -- `E_min ⊆ Star(c)`
      exact Set.union_subset_union (Set.subset_union_left.trans Set.subset_union_right)
        subset_rfl
    · -- every source is either an early one or a crossing one
      intro x hx y hy
      refine Subgraph.reachable_mono (Subgraph.fromEdgeSet_mono Set.subset_union_left)
        (hEreach x ?_ y hy)
      obtain ⟨w, hw⟩ := h.exists_earliestNeighborFn_eq_some (Or.inl hx)
      obtain ⟨k, hk⟩ := h.exists_adj_left h₂ (h.mem_right_of_earliestNeighborFn_eq_some hx hw)
      by_cases hτ : k ≤ τ
      · exact Or.inl ⟨hx, w, hw, k, hk, hτ⟩
      · exact Or.inr ⟨hx, hcross x hx ⟨w, hw, k, hk, Nat.lt_of_not_le hτ⟩⟩
  · -- (ii) some upper source `v` is not a crossing: Lemma 16 with `Ext(c) ∪ Ext(N_min v)`
    push Not at hcross
    obtain ⟨v, hv, ⟨w, hw, hτ⟩, hncross⟩ := hcross
    have hw' := Option.mem_def.1 hw
    have hreach := (h.isCutCrossing_or_reachable h₀ h₁ h₂ τ hv hw' hτ).resolve_left hncross
    refine ⟨_, Set.union_subset extStarSource_subset_edgeSet extStarTarget_subset_edgeSet,
      h.ncard_extStar_union_le h₀ h₁, ?_, Or.inr hreach⟩
    -- `E_min ∪ E_max ⊆ Ext(c)` by definition
    exact (Set.subset_union_left.trans Set.subset_union_left).trans Set.subset_union_left

@[deprecated (since := "2026-10-29")]
alias exists_reachable_half := exists_reachable_of_threshold

end Cut

section Recursion

variable [G.IsSymm] [G.IsLoopless]

/-- The recursive step of Baligács 2026, Theorem 18: suppose `E ⊆ H` contains `E_min ∪ E_max`, has
at most `6n` edges, and `fromEdgeSet E` reaches every target from every source except for a pair
in the *uncovered part* `s₂ × t₂` (one side of which has at most `n / 2` vertices). Then the
induction hypothesis `ih` on the bi-clique left uncovered, reduced to an extremally matched one by
Baligács 2026, Lemma 5, gives a one-sided spanner of `H` with at most `14 n` edges that still
contains `E_min ∪ E_max`. -/
private theorem exists_isSpannerFromTo_of_covered (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsSimple) (h₁ : H.IsProper) {n : ℕ} (hn : s.ncard = n) (hpos : 0 < n)
    {E : Set (Sym2 V × ℕ)} (hEH : E ⊆ H.edgeSet) (hEcard : E.ncard ≤ 6 * s.ncard)
    (hEM : H.eMin s ∪ H.eMax s ⊆ E)
    (ih : ∀ {H' : Subgraph G} {s' t' : Set V} [Finite H'.verts] [H'.IsSymm],
      H'.IsExtremallyMatched s' t' → H'.IsSimple → H'.IsProper → s'.ncard < n →
        ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerFromTo H' s' t' ∧
          H'.eMin s' ∪ H'.eMax s' ⊆ K.edgeSet ∧ K.edgeSet.ncard ≤ 14 * s'.ncard)
    {s₂ t₂ : Set V} (hs₂ : s₂ ⊆ s) (ht₂ : t₂ ⊆ t) (hhalf : 2 * s₂.ncard ≤ n ∨ 2 * t₂.ncard ≤ n)
    (hcovered : ∀ x ∈ s, ∀ y ∈ t, (Subgraph.fromEdgeSet G E).Reachable x y ∨ (x ∈ s₂ ∧ y ∈ t₂)) :
    ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerFromTo H s t ∧ H.eMin s ∪ H.eMax s ⊆ K.edgeSet ∧
      K.edgeSet.ncard ≤ 14 * n := by
  have hst : t.ncard = n := hn ▸ (h.ncard_eq h₁).symm
  have hsub : s ∪ t ⊆ H.verts := h.subset_verts
  have hEG : E ⊆ G.edgeSet := hEH.trans H.edgeSet_subset
  have hs₂fin : s₂.Finite := h.finite_left.subset hs₂
  have ht₂fin : t₂.Finite := h.finite_right.subset ht₂
  have hs₂n : s₂.ncard ≤ n := hn ▸ Set.ncard_le_ncard hs₂ h.finite_left
  have ht₂n : t₂.ncard ≤ n := hst ▸ Set.ncard_le_ncard ht₂ h.finite_right
  -- the remaining bi-clique `H.induce (s₂ ∪ t₂)`
  have hsub₂ : s₂ ∪ t₂ ⊆ H.verts := (Set.union_subset_union hs₂ ht₂).trans hsub
  have := Subgraph.finite_induce_verts H hsub₂
  have hle₁ : H.induce (s₂ ∪ t₂) ≤ H := Subgraph.induce_le_of_subset hsub₂
  have hbc₁ := Subgraph.isBicliqueWith_induce h.isBicliqueWith hs₂ ht₂
  -- Lemma 5: reduce it to an extremally matched bi-clique on `s' ∪ t'`
  obtain ⟨s', hs', t', ht', hverts, hem, hext⟩ := Subgraph.exists_isExtremallyMatched_reduction
    (h₀.mono (Subgraph.toTemporalGraph_le hle₁)) hbc₁
  have hle₂ : (H.induce (s₂ ∪ t₂)).induce (s' ∪ t') ≤ H :=
    (Subgraph.induce_le_of_subset hverts).trans hle₁
  have := Subgraph.finite_induce_verts _ hverts
  have hsimple := h₀.mono (Subgraph.toTemporalGraph_le hle₂)
  have hproper := h₁.mono (Subgraph.toTemporalGraph_le hle₂)
  -- `x = |s'| = |t'|` is at most `min (|s₂|, |t₂|)`, and at most `n / 2`
  have hxeq := hem.ncard_eq hproper
  have hxs := Set.ncard_le_ncard hs' hs₂fin
  have hxt := Set.ncard_le_ncard ht' ht₂fin
  -- the induction hypothesis on the smaller extremally matched bi-clique
  -- (`|s'| ≤ min (|s₂|, |t₂|) ≤ n / 2 < n`, as one of the two uncovered sides has at most `n / 2`)
  obtain ⟨K'', hK'', hK''span, -, hK''card⟩ := ih hem hsimple hproper (by omega)
  -- Lemma 5: its spanner extends to the remaining bi-clique
  obtain ⟨K₂, hK₂, hK₂span, hK₂card⟩ := hext K'' hK'' hK''span
  -- `K₂.IsSymm` as an instance, for the symmetry of `fromEdgeSet G E ⊔ K₂`
  have := hK₂
  refine ⟨Subgraph.fromEdgeSet G E ⊔ K₂, inferInstance,
    ⟨sup_le (Subgraph.fromEdgeSet_le hEH) (hK₂span.1.trans hle₁), ?_⟩, ?_, ?_⟩
  · -- a pair not reached by `fromEdgeSet E` is an edge of the remaining bi-clique, reached
    -- by `K₂`
    intro x hx y hy _
    rcases hcovered x hx y hy with hxy | ⟨hx₂, hy₂⟩
    · exact Subgraph.reachable_mono le_sup_left hxy
    · exact Subgraph.reachable_mono le_sup_right
        (hK₂span.2 x hx₂ y hy₂ (Subgraph.reachable_of_isBicliqueWith hbc₁ hx₂ hy₂))
  · -- `E_min ∪ E_max ⊆ E`
    rw [Subgraph.sup_edgeSet, Subgraph.fromEdgeSet_eq hEG]
    exact hEM.trans Set.subset_union_left
  · rw [Subgraph.sup_edgeSet, Subgraph.fromEdgeSet_eq hEG]
    have h₂ := Set.ncard_union_le E K₂.edgeSet
    -- `|E ∪ K₂| ≤ |E| + |K₂| ≤ 6 n + (14 x + 2 (|s₂| + |t₂|) - 4 x)`, and `10 x + 2 (|s₂| + |t₂|)`
    -- is at most `8 n`: `x ≤ n / 2` and `|s₂| + |t₂| ≤ n / 2 + n`
    omega

/-- Baligács 2026, Theorem 18 (covering part, with Theorem 6): an extremally matched finite simple
proper bi-clique `H` with `n = |s| = |t|` has a symmetric one-sided spanner from `s` to `t` with
at most `14 n` edges, which contains `E_min ∪ E_max`. The proof is by strong induction on `n`:
Lemma 17 at the median threshold, then Lemma 5 and the induction hypothesis on the uncovered
part, of size at most `n / 2`, for a total of `6n + (3n - 4x) + 14x ≤ 14n` edges. -/
theorem exists_isSpannerFromTo_eMin_union_eMax_subset (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsSimple) (h₁ : H.IsProper) :
    ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerFromTo H s t ∧ H.eMin s ∪ H.eMax s ⊆ K.edgeSet ∧
      K.edgeSet.ncard ≤ 14 * s.ncard := by
  -- strong induction on `n = |s|`, over all extremally matched bi-cliques
  induction hn : s.ncard using Nat.strong_induction_on generalizing H s t with
  | _ n ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
    · -- no source: the empty subgraph is a vacuous spanner
      refine ⟨Subgraph.fromEdgeSet G ∅, inferInstance,
        ⟨Subgraph.fromEdgeSet_le (Set.empty_subset _), fun x hx ↦ hx.elim⟩, ?_, ?_⟩
      · rintro e (⟨v, hv, -⟩ | ⟨v, hv, -⟩) <;> exact absurd hv (Set.notMem_empty _)
      · rw [Subgraph.fromEdgeSet_eq (Set.empty_subset _), Set.ncard_empty]
        exact Nat.zero_le _
    have hpos : 0 < n := hn ▸ (Set.ncard_pos h.finite_left).2 ⟨c, hc⟩
    have hst : t.ncard = n := hn ▸ (h.ncard_eq h₁).symm
    -- the times of the edges at `c` exist, for every target
    choose! f hf using fun u (hu : u ∈ t) ↦ h.exists_adj_left hc hu
    -- a property of the time of the edge `{c, u}` is a property of `f u`, its only time
    have hval : ∀ u ∈ t, ∀ P : ℕ → Prop, (∃ k, H.Adj c u k ∧ P k) ↔ P (f u) :=
      fun u hu _ ↦ ⟨fun ⟨_, hk, hP⟩ ↦ h₀ hk (hf u hu) ▸ hP, fun hP ↦ ⟨f u, hf u hu, hP⟩⟩
    -- cut at a median threshold `τ`, and apply Lemma 17
    obtain ⟨τ, hlow, hhigh⟩ := Set.exists_median_threshold f h.finite_right
    obtain ⟨E, hEH, hEcard, hEM, hcov⟩ := h.exists_reachable_of_threshold h₀ h₁ hc τ
    -- the recursion on the part left uncovered by `fromEdgeSet E`
    have hrecurse := fun (s₂ t₂ : Set V) hs₂ ht₂ hhalf hcovered ↦
      exists_isSpannerFromTo_of_covered h h₀ h₁ hn hpos hEH hEcard hEM
        (fun hem hs hp hlt ↦ ih _ hlt hem hs hp rfl) (s₂ := s₂) (t₂ := t₂) hs₂ ht₂ hhalf hcovered
    rcases hcov with hcov | hcov
    · -- (i) `fromEdgeSet E` reaches the targets from `τ` on: recurse on `(s, t₁)`, where
      -- `t₁ = {u ∈ t | f u < τ}` has at most `n / 2` elements
      -- `hlow` : `|{u ∈ t | f u < τ}| ≤ |t| / 2`, and `|t| = n`
      refine hrecurse s {u ∈ t | f u < τ} subset_rfl (Set.sep_subset _ _) (Or.inr (by omega)) ?_
      intro x hx y hy
      by_cases hτ : τ ≤ f y
      · exact Or.inl (hcov x hx y ⟨hy, (hval y hy _).2 hτ⟩)
      · exact Or.inr ⟨hx, hy, Nat.lt_of_not_le hτ⟩
    · -- (ii) `fromEdgeSet E` reaches every target from the early sources: recurse on `(s₁, t)`,
      -- where `s₁` is the set of the upper sources, matched by `N_min` with the late targets
      have ht₁ : {u ∈ t | ∃ k, H.Adj c u k ∧ τ < k} = {u ∈ t | τ < f u} :=
        Set.ext fun u ↦ and_congr_right fun hu ↦ hval u hu (τ < ·)
      -- `|s₁|` is the number of the targets above `τ`, which is at most `n / 2`
      have hs₁ : (H.upperSources s c τ).ncard =
          {u ∈ t | τ < f u}.ncard :=
        ht₁ ▸ h.ncard_setOf_earliestNeighborFn h₁ (fun u ↦ ∃ k, H.Adj c u k ∧ τ < k)
      -- `hs₁` and `hhigh` : `|s₁| = |{u ∈ t | τ < f u}| ≤ |t| / 2`, and `|t| = n`
      refine hrecurse (H.upperSources s c τ) t
        (Set.sep_subset _ _) subset_rfl (Or.inl (by omega)) ?_
      intro x hx y hy
      -- a source is early, or upper
      obtain ⟨w, hw⟩ := h.exists_earliestNeighborFn_eq_some (Or.inl hx)
      obtain ⟨k, hk⟩ := h.exists_adj_left hc (h.mem_right_of_earliestNeighborFn_eq_some hx hw)
      by_cases hτ : k ≤ τ
      · exact Or.inl (hcov x ⟨hx, w, hw, k, hk, hτ⟩ y hy)
      · exact Or.inr ⟨⟨hx, w, hw, k, hk, Nat.lt_of_not_le hτ⟩, hy⟩

@[deprecated (since := "2026-10-29")]
alias exists_isSpannerFromTo_aux := exists_isSpannerFromTo_eMin_union_eMax_subset

/-- Baligács 2026, Theorem 18 (with Theorem 6): an extremally matched finite simple proper
bi-clique `H` with `n = |s| = |t|` has a symmetric one-sided spanner from `s` to `t` with at most
`14 n` edges, which is moreover temporally connected on `s ∪ t`. It contains `E_min ∪ E_max`
(`exists_isSpannerFromTo_eMin_union_eMax_subset`), so a target reaches whatever its `N_min`
reaches, and a source is reached by whatever reaches its `N_max`. -/
theorem exists_isSpannerFromTo_temporallyConnected (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsSimple) (h₁ : H.IsProper) :
    ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerFromTo H s t ∧ K.TemporallyConnected (s ∪ t) ∧
      K.edgeSet.ncard ≤ 14 * s.ncard := by
  obtain ⟨K, hK, hspan, hM, hcard⟩ := h.exists_isSpannerFromTo_eMin_union_eMax_subset h₀ h₁
  have := hK
  refine ⟨K, hK, hspan, h.temporallyConnected hspan.1 (fun v hv w n he ↦ ?_)
    (fun v hv w n he ↦ ?_) fun x hx y hy ↦
      hspan.2 x hx y hy (Subgraph.reachable_of_isBicliqueWith h.isBicliqueWith hx hy), hcard⟩
  · -- the earliest edge at `v` is in `E_min`
    exact K.mem_edgeSet.1 (hM (Or.inl (h.mem_eMin_of_mem_union h₁ hv
      (he.earliestNeighborFn_eq_some h₁) he.1)))
  · -- the latest edge at `v` is in `E_max`
    exact K.mem_edgeSet.1 (hM (Or.inr (h.mem_eMax_of_mem_union h₁ hv
      (he.latestNeighborFn_eq_some h₁) he.1)))

@[deprecated (since := "2026-10-29")]
alias exists_isSpannerFromTo := exists_isSpannerFromTo_temporallyConnected

end Recursion

end IsExtremallyMatched

namespace Subgraph

variable {H : Subgraph G} [Finite H.verts] [G.IsSymm] [G.IsLoopless] [H.IsSymm]

/-- Baligács 2026, Theorem 3: a finite simple proper temporal bi-clique subgraph `H` on `s` and
`t` has a symmetric one-sided spanner from `s` to `t` with at most
`10 min(|s|, |t|) + 2 (|s| + |t|)` edges. Lemma 5 reduces `H` to an extremally matched bi-clique
with `x = |s'| = |t'| ≤ min(|s|, |t|)`, which Theorem 18 spans with `14 x` edges; Lemma 5 then
adds back `2 (|s| + |t| - 2 x)` edges. Compare `Subgraph.exists_isSpannerFromTo_ncard_le`, the
`O(n log n)` bound of SAND 2025, §4.1. -/
theorem exists_isSpannerFromTo_ncard_le_linear {s t : Set V} (h₀ : H.IsSimple)
    (h₁ : H.IsProper) (h₂ : H.IsBicliqueWith s t) :
    ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerFromTo H s t ∧
      K.edgeSet.ncard ≤ 10 * min s.ncard t.ncard + 2 * (s.ncard + t.ncard) := by
  -- Lemma 5: reduce `H` to an extremally matched bi-clique on `s' ∪ t'`
  obtain ⟨s', hs', t', ht', hverts, hem, hext⟩ := exists_isExtremallyMatched_reduction h₀ h₂
  have hle : H.induce (s' ∪ t') ≤ H := induce_le_of_subset hverts
  have := finite_induce_verts H hverts
  have hsimple := h₀.mono (toTemporalGraph_le hle)
  have hproper := h₁.mono (toTemporalGraph_le hle)
  -- Theorem 18 on the reduced bi-clique, then Lemma 5 extends its spanner to `H`
  obtain ⟨K'', hK'', hK''span, -, hK''card⟩ :=
    hem.exists_isSpannerFromTo_temporallyConnected hsimple hproper
  obtain ⟨K', hK', hK'span, hK'card⟩ := hext K'' hK'' hK''span
  refine ⟨K', hK', hK'span, ?_⟩
  have hx := hem.ncard_eq hproper
  -- `x = |s'| = |t'|` is at most `min(|s|, |t|)`
  have hxmin : s'.ncard ≤ min s.ncard t.ncard := by
    rcases Nat.eq_zero_or_pos s'.ncard with h₃ | h₃
    · -- `x = 0 ≤ min (|s|, |t|)`
      omega
    · -- `x > 0`: `s'` and `t'` are nonempty, so `s ∪ t ⊆ H.verts` is finite
      have hs'ne : s'.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
      have ht'ne : t'.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
      have hsub : s ∪ t ⊆ H.verts :=
        isBicliqueWith_subset_verts h₂ (hs'ne.mono hs') (ht'ne.mono ht')
      have hsle := Set.ncard_le_ncard hs'
        ((Set.toFinite H.verts).subset (Set.subset_union_left.trans hsub))
      have htle := Set.ncard_le_ncard ht'
        ((Set.toFinite H.verts).subset (Set.subset_union_right.trans hsub))
      -- `x = |s'| ≤ |s|` and `x = |t'| ≤ |t|`
      omega
  -- `|K'| + 4 x ≤ 14 x + 2 (|s| + |t|)`, so `|K'| ≤ 10 x + 2 (|s| + |t|)`, and `x ≤ min (|s|, |t|)`
  omega

end Subgraph

end TemporalGraph
