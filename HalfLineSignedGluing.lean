import LeanVerification.LocalSignedEncoding

/-! The manuscript's arbitrary compatible finite signed measures on bounded
half-line intervals give actual locally finite global Jordan variations. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace LeanVerification.LocalSigned

def halfLineChart (n : ℕ) : Set ℝ := Icc 0 n

theorem measurableSet_halfLineChart (n : ℕ) : MeasurableSet (halfLineChart n) := measurableSet_Icc

theorem iUnion_halfLineChart : (⋃ n, halfLineChart n) = Ici (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact hn.1
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_gt x
    exact mem_iUnion.mpr ⟨n, hx, hn.le⟩

theorem halfLine_variation_supported (ν : ℕ → SignedMeasure ℝ) :
    (variationGlue halfLineChart ν).restrict (Ici 0) = variationGlue halfLineChart ν := by
  simpa only [iUnion_halfLineChart] using variationGlue_supported halfLineChart ν measurableSet_halfLineChart

theorem halfLine_variation_locallyFinite (ν : ℕ → SignedMeasure ℝ)
    (hc : Compatible halfLineChart ν) :
    IsLocallyFiniteMeasure (variationGlue halfLineChart ν) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt x
  refine ⟨Iio (n : ℝ), isOpen_Iio.mem_nhds hn, ?_⟩
  have he := congrArg (fun μ : Measure ℝ => μ (Iio (n : ℝ))) (halfLine_variation_supported ν)
  dsimp only at he
  rw [Measure.restrict_apply measurableSet_Iio] at he
  rw [← he]
  apply (measure_mono (show Iio (n : ℝ) ∩ Ici 0 ⊆ halfLineChart n from ?_)).trans_lt
    (variationGlue_finite_on_chart halfLineChart ν measurableSet_halfLineChart hc n)
  intro y hy
  exact ⟨hy.2, hy.1.le⟩

theorem halfLine_variation_nonnegative_support (ν : ℕ → SignedMeasure ℝ) :
    ∀ᵐ x ∂variationGlue halfLineChart ν, 0 ≤ x := by
  rw [ae_iff]
  change variationGlue halfLineChart ν (Ici (0 : ℝ))ᶜ = 0
  have he := congrArg (fun μ : Measure ℝ => μ (Ici (0 : ℝ))ᶜ) (halfLine_variation_supported ν)
  dsimp only at he
  rw [Measure.restrict_apply measurableSet_Ici.compl, compl_inter_self, measure_empty] at he
  exact he.symm

theorem halfLine_positive_locallyFinite (ν : ℕ → SignedMeasure ℝ)
    (hc : Compatible halfLineChart ν) : IsLocallyFiniteMeasure (positiveGlue halfLineChart ν) := by
  letI := halfLine_variation_locallyFinite ν hc
  exact Measure.isLocallyFiniteMeasure_of_le (show positiveGlue halfLineChart ν ≤ variationGlue halfLineChart ν from
    Measure.le_add_right le_rfl)

theorem halfLine_negative_locallyFinite (ν : ℕ → SignedMeasure ℝ)
    (hc : Compatible halfLineChart ν) : IsLocallyFiniteMeasure (negativeGlue halfLineChart ν) := by
  letI := halfLine_variation_locallyFinite ν hc
  exact Measure.isLocallyFiniteMeasure_of_le (show negativeGlue halfLineChart ν ≤ variationGlue halfLineChart ν from
    Measure.le_add_left le_rfl)

theorem halfLine_gluing_complete (ν : ℕ → SignedMeasure ℝ)
    (hc : Compatible halfLineChart ν) :
    positiveGlue halfLineChart ν ⟂ₘ negativeGlue halfLineChart ν ∧
    IsLocallyFiniteMeasure (variationGlue halfLineChart ν) ∧
    SigmaFinite (variationGlue halfLineChart ν) ∧
    (∀ n, (variationGlue halfLineChart ν).restrict (halfLineChart n) =
      (ν n).totalVariation.restrict (halfLineChart n)) ∧
    (∀ n t, MeasurableSet t → t ⊆ halfLineChart n →
      (positiveGlue halfLineChart ν).real t - (negativeGlue halfLineChart ν).real t = ν n t) := by
  exact ⟨glued_mutuallySingular _ _ measurableSet_halfLineChart,
    halfLine_variation_locallyFinite ν hc,
    variationGlue_sigmaFinite _ _ measurableSet_halfLineChart hc,
    variationGlue_restrict _ _ measurableSet_halfLineChart hc,
    fun n t ht hsub => glued_signed_value _ _ measurableSet_halfLineChart hc n ht hsub⟩

theorem bounded_interval_positive_recovery (ν : ℝ → SignedMeasure ℝ)
    (hc : ∀ R S : ℝ, 0 ≤ R → 0 ≤ S →
      (ν R).restrict (Icc 0 R ∩ Icc 0 S) = (ν S).restrict (Icc 0 R ∩ Icc 0 S))
    (R : ℝ) (hR : 0 ≤ R) :
    (positiveGlue halfLineChart (fun n => ν n)).restrict (Icc 0 R) =
      (ν R).toJordanDecomposition.posPart.restrict (Icc 0 R) := by
  apply measureGlue_restrict_other halfLineChart _ measurableSet_halfLineChart measurableSet_Icc
    (by rw [iUnion_halfLineChart]; exact Icc_subset_Ici_self)
  intro n
  exact positive_restrict_eq_of_signed_restrict_eq _ _ (measurableSet_Icc.inter measurableSet_Icc)
    (hc n R (Nat.cast_nonneg n) hR)

theorem bounded_interval_negative_recovery (ν : ℝ → SignedMeasure ℝ)
    (hc : ∀ R S : ℝ, 0 ≤ R → 0 ≤ S →
      (ν R).restrict (Icc 0 R ∩ Icc 0 S) = (ν S).restrict (Icc 0 R ∩ Icc 0 S))
    (R : ℝ) (hR : 0 ≤ R) :
    (negativeGlue halfLineChart (fun n => ν n)).restrict (Icc 0 R) =
      (ν R).toJordanDecomposition.negPart.restrict (Icc 0 R) := by
  apply measureGlue_restrict_other halfLineChart _ measurableSet_halfLineChart measurableSet_Icc
    (by rw [iUnion_halfLineChart]; exact Icc_subset_Ici_self)
  intro n
  exact negative_restrict_eq_of_signed_restrict_eq _ _ (measurableSet_Icc.inter measurableSet_Icc)
    (hc n R (Nat.cast_nonneg n) hR)

theorem arbitrary_bounded_interval_data (ν : ℝ → SignedMeasure ℝ)
    (hc : ∀ R S : ℝ, 0 ≤ R → 0 ≤ S →
      (ν R).restrict (Icc 0 R ∩ Icc 0 S) = (ν S).restrict (Icc 0 R ∩ Icc 0 S)) :
    ∃! pair : Measure ℝ × Measure ℝ,
      pair.1 ⟂ₘ pair.2 ∧ IsLocallyFiniteMeasure (pair.1 + pair.2) ∧
      pair.1.restrict (Ici 0) = pair.1 ∧ pair.2.restrict (Ici 0) = pair.2 ∧
      (∀ R : ℝ, 0 ≤ R → pair.1.restrict (Icc 0 R) =
        (ν R).toJordanDecomposition.posPart.restrict (Icc 0 R)) ∧
      (∀ R : ℝ, 0 ≤ R → pair.2.restrict (Icc 0 R) =
        (ν R).toJordanDecomposition.negPart.restrict (Icc 0 R)) := by
  have hnat : Compatible halfLineChart (fun n => ν n) :=
    fun n m => hc n m (Nat.cast_nonneg n) (Nat.cast_nonneg m)
  refine ⟨(positiveGlue halfLineChart (fun n => ν n), negativeGlue halfLineChart (fun n => ν n)), ?_, ?_⟩
  · refine ⟨glued_mutuallySingular _ _ measurableSet_halfLineChart,
      halfLine_variation_locallyFinite _ hnat, ?_, ?_,
      bounded_interval_positive_recovery ν hc, bounded_interval_negative_recovery ν hc⟩
    · simpa only [iUnion_halfLineChart] using positiveGlue_supported halfLineChart
        (fun n => ν n) measurableSet_halfLineChart
    · simpa only [iUnion_halfLineChart] using negativeGlue_supported halfLineChart
        (fun n => ν n) measurableSet_halfLineChart
  · intro pair hp
    apply Prod.ext
    · apply positiveGlue_unique halfLineChart (fun n => ν n) measurableSet_halfLineChart hnat
      · simpa only [iUnion_halfLineChart] using hp.2.2.1
      · intro n
        exact hp.2.2.2.2.1 n (Nat.cast_nonneg n)
    · apply negativeGlue_unique halfLineChart (fun n => ν n) measurableSet_halfLineChart hnat
      · simpa only [iUnion_halfLineChart] using hp.2.2.2.1
      · intro n
        exact hp.2.2.2.2.2 n (Nat.cast_nonneg n)

theorem glued_cauchy_cumulative (ν : ℕ → SignedMeasure ℝ)
    (hc : Compatible halfLineChart ν) {δ : ℝ} (hδ : 0 < δ)
    (hint : Integrable (fun s : ℝ => 1 / (1 + s)) (variationGlue halfLineChart ν)) :
    (∫ s, 1 / (δ + s) ∂positiveGlue halfLineChart ν) -
      (∫ s, 1 / (δ + s) ∂negativeGlue halfLineChart ν) =
      ∫ t in Ici 0, (∫ s in Iic t,
        Stieltjes.signedDensity (glued_mutuallySingular halfLineChart ν measurableSet_halfLineChart) s
          ∂variationGlue halfLineChart ν) / (δ + t)^2 := by
  letI := halfLine_positive_locallyFinite ν hc
  letI := halfLine_negative_locallyFinite ν hc
  exact Stieltjes.cauchy_cumulative_jordan_pair
    (glued_mutuallySingular halfLineChart ν measurableSet_halfLineChart)
    hδ (halfLine_variation_nonnegative_support ν) hint

end LeanVerification.LocalSigned
