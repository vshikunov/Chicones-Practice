import LeanVerification.SignedJordanRestriction
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! Gluing arbitrary compatible positive local measures on countable covers. -/

noncomputable section

open MeasureTheory Set

namespace LeanVerification.LocalSigned

variable {α : Type*} [MeasurableSpace α]

def measureGlue (s : ℕ → Set α) (μ : ℕ → Measure α) : Measure α :=
  Measure.sum fun n => (μ n).restrict (disjointed s n)

theorem restrict_eq_on_refinement {μ ν : Measure α} {s t : Set α}
    (h : μ.restrict s = ν.restrict s) (hst : t ⊆ s) :
    μ.restrict t = ν.restrict t := by
  calc
    μ.restrict t = (μ.restrict s).restrict t := (Measure.restrict_restrict_of_subset hst).symm
    _ = (ν.restrict s).restrict t := congrArg (fun ρ : Measure α => ρ.restrict t) h
    _ = ν.restrict t := Measure.restrict_restrict_of_subset hst

theorem measureGlue_restrict (s : ℕ → Set α) (μ : ℕ → Measure α)
    (hs : ∀ n, MeasurableSet (s n))
    (hc : ∀ i j, (μ i).restrict (s i ∩ s j) = (μ j).restrict (s i ∩ s j))
    (j : ℕ) :
    (measureGlue s μ).restrict (s j) = (μ j).restrict (s j) := by
  have ha : ∀ n, MeasurableSet (disjointed s n) := MeasurableSet.disjointed hs
  have he (n : ℕ) : ((μ n).restrict (disjointed s n)).restrict (s j) =
      ((μ j).restrict (s j)).restrict (disjointed s n) := by
    rw [Measure.restrict_restrict (hs j), Measure.restrict_restrict (ha n)]
    rw [inter_comm (s j)]
    exact restrict_eq_on_refinement (hc n j) (inter_subset_inter (disjointed_subset _ _) subset_rfl)
  rw [measureGlue, Measure.restrict_sum_of_countable]
  simp_rw [he]
  rw [← Measure.restrict_iUnion (disjoint_disjointed s) ha, iUnion_disjointed,
    Measure.restrict_restrict (MeasurableSet.iUnion hs)]
  rw [inter_eq_right.mpr (subset_iUnion s j)]

theorem measureGlue_restrict_other (s : ℕ → Set α) (μ : ℕ → Measure α)
    (hs : ∀ n, MeasurableSet (s n)) {t : Set α} (ht : MeasurableSet t)
    (hts : t ⊆ ⋃ n, s n) (ρ : Measure α)
    (hc : ∀ n, (μ n).restrict (s n ∩ t) = ρ.restrict (s n ∩ t)) :
    (measureGlue s μ).restrict t = ρ.restrict t := by
  have ha : ∀ n, MeasurableSet (disjointed s n) := MeasurableSet.disjointed hs
  have he (n : ℕ) : ((μ n).restrict (disjointed s n)).restrict t =
      (ρ.restrict t).restrict (disjointed s n) := by
    rw [Measure.restrict_restrict ht, Measure.restrict_restrict (ha n)]
    rw [inter_comm t]
    exact restrict_eq_on_refinement (hc n) (inter_subset_inter (disjointed_subset _ _) subset_rfl)
  rw [measureGlue, Measure.restrict_sum_of_countable]
  simp_rw [he]
  rw [← Measure.restrict_iUnion (disjoint_disjointed s) ha, iUnion_disjointed,
    Measure.restrict_restrict (MeasurableSet.iUnion hs), inter_eq_right.mpr hts]

theorem measureGlue_supported (s : ℕ → Set α) (μ : ℕ → Measure α)
    (hs : ∀ n, MeasurableSet (s n)) :
    (measureGlue s μ).restrict (⋃ n, s n) = measureGlue s μ := by
  rw [measureGlue, Measure.restrict_sum_of_countable]
  congr 1
  funext n
  rw [Measure.restrict_restrict (MeasurableSet.iUnion hs)]
  rw [inter_eq_right.mpr ((disjointed_subset s n).trans (subset_iUnion s n))]

theorem measureGlue_unique (s : ℕ → Set α) (μ : ℕ → Measure α)
    (hs : ∀ n, MeasurableSet (s n))
    (hc : ∀ i j, (μ i).restrict (s i ∩ s j) = (μ j).restrict (s i ∩ s j))
    {ρ : Measure α} (hsupp : ρ.restrict (⋃ n, s n) = ρ)
    (hρ : ∀ n, ρ.restrict (s n) = (μ n).restrict (s n)) :
    ρ = measureGlue s μ := by
  rw [← hsupp, ← measureGlue_supported s μ hs]
  apply Measure.restrict_iUnion_congr.mpr
  intro n
  rw [hρ n, measureGlue_restrict s μ hs hc n]

theorem mutuallySingular_restrict_disjoint {μ ν : Measure α} {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t) :
    μ.restrict s ⟂ₘ ν.restrict t := by
  refine ⟨t, ht, ?_, ?_⟩
  · rw [Measure.restrict_apply ht, inter_comm, hd.inter_eq, measure_empty]
  · rw [Measure.restrict_apply ht.compl, compl_inter_self, measure_empty]

theorem measureGlue_mutuallySingular (s : ℕ → Set α) (μ ν : ℕ → Measure α)
    (hs : ∀ n, MeasurableSet (s n)) (h : ∀ n, μ n ⟂ₘ ν n) :
    measureGlue s μ ⟂ₘ measureGlue s ν := by
  rw [measureGlue, measureGlue, Measure.MutuallySingular.sum_left]
  intro i
  rw [Measure.MutuallySingular.sum_right]
  intro j
  by_cases hij : i = j
  · subst j
    exact (((h i).restrict _).symm.restrict _).symm
  · exact mutuallySingular_restrict_disjoint (MeasurableSet.disjointed hs i)
      (MeasurableSet.disjointed hs j) (disjoint_disjointed s hij)

end LeanVerification.LocalSigned
