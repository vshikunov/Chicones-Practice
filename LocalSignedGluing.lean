import LeanVerification.LocalMeasureGluing
import LeanVerification.SignedInput

/-! Canonical global Jordan variations from arbitrary compatible local signed measures.
The global positive and negative variations can both have infinite mass. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace LeanVerification.LocalSigned

variable {α : Type*} [MeasurableSpace α]

def positiveGlue (s : ℕ → Set α) (ν : ℕ → SignedMeasure α) : Measure α :=
  measureGlue s fun n => (ν n).toJordanDecomposition.posPart

def negativeGlue (s : ℕ → Set α) (ν : ℕ → SignedMeasure α) : Measure α :=
  measureGlue s fun n => (ν n).toJordanDecomposition.negPart

def variationGlue (s : ℕ → Set α) (ν : ℕ → SignedMeasure α) : Measure α :=
  positiveGlue s ν + negativeGlue s ν

def Compatible (s : ℕ → Set α) (ν : ℕ → SignedMeasure α) : Prop :=
  ∀ i j, (ν i).restrict (s i ∩ s j) = (ν j).restrict (s i ∩ s j)

theorem positiveGlue_restrict (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) (hc : Compatible s ν) (j : ℕ) :
    (positiveGlue s ν).restrict (s j) = (ν j).toJordanDecomposition.posPart.restrict (s j) := by
  apply measureGlue_restrict s _ hs
  intro i k
  exact positive_restrict_eq_of_signed_restrict_eq _ _ ((hs i).inter (hs k)) (hc i k)

theorem negativeGlue_restrict (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) (hc : Compatible s ν) (j : ℕ) :
    (negativeGlue s ν).restrict (s j) = (ν j).toJordanDecomposition.negPart.restrict (s j) := by
  apply measureGlue_restrict s _ hs
  intro i k
  exact negative_restrict_eq_of_signed_restrict_eq _ _ ((hs i).inter (hs k)) (hc i k)

theorem variationGlue_restrict (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) (hc : Compatible s ν) (j : ℕ) :
    (variationGlue s ν).restrict (s j) = (ν j).totalVariation.restrict (s j) := by
  rw [variationGlue, Measure.restrict_add, positiveGlue_restrict s ν hs hc j,
    negativeGlue_restrict s ν hs hc j, SignedMeasure.totalVariation, Measure.restrict_add]

theorem glued_signed_value (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) (hc : Compatible s ν) (j : ℕ)
    {t : Set α} (ht : MeasurableSet t) (hts : t ⊆ s j) :
    (positiveGlue s ν).real t - (negativeGlue s ν).real t = ν j t := by
  have hp := congrArg (fun μ : Measure α => μ t) (positiveGlue_restrict s ν hs hc j)
  have hn := congrArg (fun μ : Measure α => μ t) (negativeGlue_restrict s ν hs hc j)
  simp only [Measure.restrict_eq_self _ hts] at hp hn
  rw [measureReal_def, measureReal_def, hp, hn]
  conv_rhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition (ν j)]
  rw [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply ht, measureReal_def,
    measureReal_def]

theorem glued_mutuallySingular (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) : positiveGlue s ν ⟂ₘ negativeGlue s ν := by
  exact measureGlue_mutuallySingular s _ _ hs fun n => (ν n).toJordanDecomposition.mutuallySingular

theorem positiveGlue_supported (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) :
    (positiveGlue s ν).restrict (⋃ n, s n) = positiveGlue s ν :=
  measureGlue_supported s _ hs

theorem negativeGlue_supported (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) :
    (negativeGlue s ν).restrict (⋃ n, s n) = negativeGlue s ν :=
  measureGlue_supported s _ hs

theorem variationGlue_supported (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) :
    (variationGlue s ν).restrict (⋃ n, s n) = variationGlue s ν := by
  rw [variationGlue, Measure.restrict_add, positiveGlue_supported s ν hs,
    negativeGlue_supported s ν hs]

theorem positiveGlue_unique (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) (hc : Compatible s ν)
    {ρ : Measure α} (hsupp : ρ.restrict (⋃ n, s n) = ρ)
    (hρ : ∀ n, ρ.restrict (s n) = (ν n).toJordanDecomposition.posPart.restrict (s n)) :
    ρ = positiveGlue s ν := by
  apply measureGlue_unique s _ hs _ hsupp hρ
  intro i j
  exact positive_restrict_eq_of_signed_restrict_eq _ _ ((hs i).inter (hs j)) (hc i j)

theorem negativeGlue_unique (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) (hc : Compatible s ν)
    {ρ : Measure α} (hsupp : ρ.restrict (⋃ n, s n) = ρ)
    (hρ : ∀ n, ρ.restrict (s n) = (ν n).toJordanDecomposition.negPart.restrict (s n)) :
    ρ = negativeGlue s ν := by
  apply measureGlue_unique s _ hs _ hsupp hρ
  intro i j
  exact negative_restrict_eq_of_signed_restrict_eq _ _ ((hs i).inter (hs j)) (hc i j)

theorem variationGlue_finite_on_chart (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) (hc : Compatible s ν) (j : ℕ) :
    variationGlue s ν (s j) < ∞ := by
  have he := congrArg (fun μ : Measure α => μ univ) (variationGlue_restrict s ν hs hc j)
  simp only [Measure.restrict_apply_univ] at he
  rw [he, SignedMeasure.totalVariation, Measure.add_apply]
  exact ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, measure_lt_top _ _⟩

theorem variationGlue_sigmaFinite (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) (hc : Compatible s ν) :
    SigmaFinite (variationGlue s ν) := by
  have hzero : variationGlue s ν (⋃ n, s n)ᶜ = 0 := by
    rw [← variationGlue_supported s ν hs, Measure.restrict_apply (MeasurableSet.iUnion hs).compl]
    rw [compl_inter_self, measure_empty]
  refine ⟨⟨⟨fun n => s n ∪ (⋃ n, s n)ᶜ, fun _ => trivial, ?_, ?_⟩⟩⟩
  · intro n
    exact (measure_union_le _ _).trans_lt (by
      rw [hzero, add_zero]
      exact variationGlue_finite_on_chart s ν hs hc n)
  · change (⋃ n, s n ∪ (⋃ n, s n)ᶜ) = univ
    rw [← iUnion_union, union_compl_self]

theorem variationGlue_locallyFinite [TopologicalSpace α]
    (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) (hc : Compatible s ν)
    (hnhds : ∀ x, ∃ n, s n ∈ 𝓝 x) : IsLocallyFiniteMeasure (variationGlue s ν) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨n, hn⟩ := hnhds x
  exact ⟨s n, hn, variationGlue_finite_on_chart s ν hs hc n⟩

theorem signed_gluing_exists_unique (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) (hc : Compatible s ν) :
    ∃! pair : Measure α × Measure α,
      pair.1 ⟂ₘ pair.2 ∧
      pair.1.restrict (⋃ n, s n) = pair.1 ∧ pair.2.restrict (⋃ n, s n) = pair.2 ∧
      (∀ n, pair.1.restrict (s n) = (ν n).toJordanDecomposition.posPart.restrict (s n)) ∧
      (∀ n, pair.2.restrict (s n) = (ν n).toJordanDecomposition.negPart.restrict (s n)) := by
  refine ⟨(positiveGlue s ν, negativeGlue s ν), ?_, ?_⟩
  · exact ⟨glued_mutuallySingular s ν hs, positiveGlue_supported s ν hs,
      negativeGlue_supported s ν hs, positiveGlue_restrict s ν hs hc,
      negativeGlue_restrict s ν hs hc⟩
  · intro pair hp
    exact Prod.ext (positiveGlue_unique s ν hs hc hp.2.1 hp.2.2.2.1)
      (negativeGlue_unique s ν hs hc hp.2.2.1 hp.2.2.2.2)

end LeanVerification.LocalSigned
