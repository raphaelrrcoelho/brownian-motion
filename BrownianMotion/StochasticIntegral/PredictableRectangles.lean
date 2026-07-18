/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.SimpleProcess
public import Mathlib.MeasureTheory.SetSemiring

/-! # Predictable rectangles

The **predictable rectangles** on `ι × Ω` are the sets `(s, t] × B` with `s < t` and
`B ∈ 𝓕 s`, together with the sets `{⊥} × B` for `B ∈ 𝓕 ⊥`. They form a semi-ring of sets
(`predictableRectangles_isSetSemiring`) and generate the elementary predictable sets
(`ElementaryPredictableSet`).

## Main definitions

- `ProbabilityTheory.predictableRectangles`: the class of predictable rectangles.

## Main statements

- `ProbabilityTheory.predictableRectangles_isSetSemiring`: the predictable rectangles form a
  semi-ring of sets.
- `ProbabilityTheory.ElementaryPredictableSet.isFiniteUnion_predictableRectangles`: every
  elementary predictable set is a finite union of predictable rectangles.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω}
  {𝓕 : Filtration ι mΩ}

/-- The class of **predictable rectangles**: sets `(s, t] × B` with `s < t` and `B ∈ 𝓕 s`,
together with `{⊥} × B` for `B ∈ 𝓕 ⊥`. -/
def predictableRectangles (𝓕 : Filtration ι mΩ) : Set (Set (ι × Ω)) :=
  {C | (∃ B, MeasurableSet[𝓕 ⊥] B ∧ C = {⊥} ×ˢ B) ∨
       (∃ s t B, s < t ∧ MeasurableSet[𝓕 s] B ∧ C = Ioc s t ×ˢ B)}

lemma singletonBot_prod_mem_predictableRectangles {B : Set Ω} (hB : MeasurableSet[𝓕 ⊥] B) :
    {⊥} ×ˢ B ∈ predictableRectangles 𝓕 :=
  Or.inl ⟨B, hB, rfl⟩

lemma empty_mem_predictableRectangles : (∅ : Set (ι × Ω)) ∈ predictableRectangles 𝓕 :=
  Or.inl ⟨∅, @MeasurableSet.empty Ω (𝓕 ⊥), by simp⟩

/-- `Ioc s t ×ˢ B` is a predictable rectangle whenever `B ∈ 𝓕 s` (it is empty when `t ≤ s`). -/
lemma Ioc_prod_mem_predictableRectangles {s t : ι} {B : Set Ω} (hB : MeasurableSet[𝓕 s] B) :
    Ioc s t ×ˢ B ∈ predictableRectangles 𝓕 := by
  rcases lt_or_ge s t with h | h
  · exact Or.inr ⟨s, t, B, h, hB, rfl⟩
  · rw [Ioc_eq_empty (not_lt.2 h), empty_prod]
    exact empty_mem_predictableRectangles

/-- The predictable rectangles form a semi-ring of sets. -/
theorem predictableRectangles_isSetSemiring : IsSetSemiring (predictableRectangles 𝓕) where
  empty_mem := empty_mem_predictableRectangles
  inter_mem := by
    rintro _ (⟨B, hB, rfl⟩ | ⟨s, t, B, -, hB, rfl⟩) _
      (⟨B', hB', rfl⟩ | ⟨s', t', B', -, hB', rfl⟩)
    · -- `{⊥}×B ∩ {⊥}×B' = {⊥}×(B∩B')`
      rw [prod_inter_prod, inter_self]
      exact singletonBot_prod_mem_predictableRectangles (hB.inter hB')
    · -- `{⊥}×B ∩ Ioc s' t'×B' = ∅` (disjoint time coordinate)
      rw [prod_inter_prod, singleton_inter_eq_empty.2 fun h ↦ not_lt_bot (mem_Ioc.1 h).1,
        empty_prod]
      exact empty_mem_predictableRectangles
    · -- `Ioc s t×B ∩ {⊥}×B' = ∅`
      rw [prod_inter_prod, inter_comm (Ioc s t),
        singleton_inter_eq_empty.2 fun h ↦ not_lt_bot (mem_Ioc.1 h).1, empty_prod]
      exact empty_mem_predictableRectangles
    · -- `Ioc s t×B ∩ Ioc s' t'×B' = Ioc (s⊔s') (t⊓t') × (B∩B')`
      rw [prod_inter_prod, Ioc_inter_Ioc]
      exact Ioc_prod_mem_predictableRectangles
        ((𝓕.mono (le_max_left s s') _ hB).inter (𝓕.mono (le_max_right s s') _ hB'))
  sdiff_eq_sUnion' := by
    -- product-difference grouped so each piece keeps a valid `𝓕`-measurable base:
    have hpd (P R : Set ι) (Q S : Set Ω) :
        (P ×ˢ Q) \ (R ×ˢ S) = (P \ R) ×ˢ Q ∪ (P ∩ R) ×ˢ (Q \ S) := by
      ext ⟨x, y⟩; simp only [mem_sdiff, mem_prod, mem_union, mem_inter_iff, not_and]; tauto
    have hbot {s' t' : ι} : ({⊥} : Set ι) ∩ Ioc s' t' = ∅ :=
      singleton_inter_eq_empty.2 fun h ↦ not_lt_bot (mem_Ioc.1 h).1
    rintro _ (⟨B, hB, rfl⟩ | ⟨s, t, B, -, hB, rfl⟩) _
      (⟨B', hB', rfl⟩ | ⟨s', t', B', hst', hB', rfl⟩)
    · -- `{⊥}×B \ {⊥}×B' = {⊥}×(B\B')`
      refine ⟨{{⊥} ×ˢ (B \ B')}, ?_, by simp, ?_⟩
      · simpa using singletonBot_prod_mem_predictableRectangles (hB.diff hB')
      · rw [Finset.coe_singleton, sUnion_singleton, hpd {⊥} {⊥} B B']; simp
    · -- `{⊥}×B \ Ioc s' t'×B' = {⊥}×B` (disjoint time coordinate)
      refine ⟨{{⊥} ×ˢ B}, ?_, by simp, ?_⟩
      · simpa using singletonBot_prod_mem_predictableRectangles hB
      · rw [Finset.coe_singleton, sUnion_singleton,
          sdiff_eq_left.mpr ((disjoint_iff_inter_eq_empty.2 hbot).set_prod_left _ _)]
    · -- `Ioc s t×B \ {⊥}×B' = Ioc s t×B` (disjoint time coordinate)
      refine ⟨{Ioc s t ×ˢ B}, ?_, by simp, ?_⟩
      · simpa using Ioc_prod_mem_predictableRectangles hB
      · rw [Finset.coe_singleton, sUnion_singleton, sdiff_eq_left.mpr
          ((disjoint_iff_inter_eq_empty.2 (by rw [inter_comm]; exact hbot)).set_prod_left _ _)]
    · -- `Ioc s t×B \ Ioc s' t'×B'` splits into ≤3 disjoint rectangles
      have hdiff : Ioc s t \ Ioc s' t' = Ioc s (min t s') ∪ Ioc (max s t') t := by
        ext x; simp only [mem_sdiff, mem_Ioc, mem_union]; grind
      refine ⟨{Ioc s (min t s') ×ˢ B, Ioc (max s t') t ×ˢ B,
        Ioc (max s s') (min t t') ×ˢ (B \ B')}, ?_, ?_, ?_⟩
      · simp only [Finset.coe_insert, Finset.coe_singleton, insert_subset_iff,
          singleton_subset_iff]
        exact ⟨Ioc_prod_mem_predictableRectangles hB,
          Ioc_prod_mem_predictableRectangles (𝓕.mono (le_max_left s t') _ hB),
          Ioc_prod_mem_predictableRectangles
            ((𝓕.mono (le_max_left s s') _ hB).diff (𝓕.mono (le_max_right s s') _ hB'))⟩
      · simp only [Finset.coe_insert, Finset.coe_singleton]
        rw [pairwiseDisjoint_insert, pairwiseDisjoint_insert]
        refine ⟨⟨by simp, ?_⟩, ?_⟩
        · rintro j hj -
          rw [mem_singleton_iff] at hj; subst hj
          exact (Ioc_disjoint_Ioc.mpr (by grind)).set_prod_left _ _
        · rintro j hj -
          simp only [mem_insert_iff, mem_singleton_iff] at hj
          rcases hj with rfl | rfl
          · exact (Ioc_disjoint_Ioc.mpr (by grind)).set_prod_left _ _
          · exact (Ioc_disjoint_Ioc.mpr (by grind)).set_prod_left _ _
      · rw [hpd (Ioc s t) (Ioc s' t') B B', hdiff, union_prod, Ioc_inter_Ioc, Finset.coe_insert,
          Finset.coe_insert, Finset.coe_singleton, sUnion_insert, sUnion_insert, sUnion_singleton,
          union_assoc]

/-- Every elementary predictable set is a finite union of predictable rectangles. -/
theorem ElementaryPredictableSet.isFiniteUnion_predictableRectangles
    (S : ElementaryPredictableSet 𝓕) :
    ∃ I : Finset (Set (ι × Ω)), ↑I ⊆ predictableRectangles 𝓕 ∧ (S : Set (ι × Ω)) = ⋃₀ I := by
  refine ⟨insert ({⊥} ×ˢ S.setBot) (S.I.image fun p ↦ Ioc p.1 p.2 ×ˢ S.set p), ?_, ?_⟩
  · intro C hC
    simp only [Finset.coe_insert, Finset.coe_image, mem_insert_iff, mem_image,
      Finset.mem_coe] at hC
    obtain rfl | ⟨p, hp, rfl⟩ := hC
    · exact singletonBot_prod_mem_predictableRectangles S.measurableSet_setBot
    · exact Ioc_prod_mem_predictableRectangles (S.measurableSet_set p hp)
  · show S.toSet = _
    rw [ElementaryPredictableSet.toSet, Finset.coe_insert, sUnion_insert, Finset.coe_image,
      sUnion_image]
    simp

end ProbabilityTheory
