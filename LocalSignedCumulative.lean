import LeanVerification.HalfLineSignedGluing

/-! The cumulative function of arbitrary compatible local signed data is the
integrated sign density of its constructed global variation measure. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace LeanVerification.LocalSigned

variable {α : Type*} [MeasurableSpace α]

theorem jordanSign_setIntegral {μ ν : Measure α} (h : μ ⟂ₘ ν)
    {s : Set α} (hs : MeasurableSet s) (hfin : (μ + ν) s < ∞) :
    (∫ x in s, jordanSign h x ∂(μ + ν)) = μ.real s - ν.real s := by
  have hi : Integrable (s.indicator (fun _ : α => (1 : ℝ))) (μ + ν) := by
    rw [integrable_indicator_iff hs]
    exact integrableOn_const.mpr (Or.inr hfin)
  have he := integral_jordanSign_encoding h hi
  have hid : (fun x => jordanSign h x • s.indicator (fun _ : α => (1 : ℝ)) x) =
      s.indicator (jordanSign h) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hid] at he
  simpa only [integral_indicator hs, setIntegral_const, smul_eq_mul, mul_one] using he

theorem halfLine_restrict_initial_interval (ν : ℕ → SignedMeasure ℝ) (t : ℝ) :
    (variationGlue halfLineChart ν).restrict (Iic t) =
      (variationGlue halfLineChart ν).restrict (Icc 0 t) := by
  calc
    (variationGlue halfLineChart ν).restrict (Iic t) =
        ((variationGlue halfLineChart ν).restrict (Ici 0)).restrict (Iic t) := by
          rw [halfLine_variation_supported]
    _ = (variationGlue halfLineChart ν).restrict (Iic t ∩ Ici 0) :=
      Measure.restrict_restrict measurableSet_Iic
    _ = (variationGlue halfLineChart ν).restrict (Icc 0 t) := by
      congr 1
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ici, mem_Icc, and_comm]

theorem glued_cumulative_local_value (ν : ℕ → SignedMeasure ℝ)
    (hc : Compatible halfLineChart ν) (n : ℕ) (t : ℝ) (ht : t ≤ n) :
    (∫ x in Iic t, jordanSign
      (glued_mutuallySingular halfLineChart ν measurableSet_halfLineChart) x
        ∂variationGlue halfLineChart ν) = ν n (Icc 0 t) := by
  have hsub : Icc (0 : ℝ) t ⊆ halfLineChart n := fun x hx => ⟨hx.1, hx.2.trans ht⟩
  have hfin : variationGlue halfLineChart ν (Icc 0 t) < ∞ :=
    (measure_mono hsub).trans_lt
      (variationGlue_finite_on_chart halfLineChart ν measurableSet_halfLineChart hc n)
  rw [halfLine_restrict_initial_interval]
  change (∫ x in Icc 0 t, jordanSign
    (glued_mutuallySingular halfLineChart ν measurableSet_halfLineChart) x
      ∂(positiveGlue halfLineChart ν + negativeGlue halfLineChart ν)) = ν n (Icc 0 t)
  rw [jordanSign_setIntegral _ measurableSet_Icc hfin]
  exact glued_signed_value _ _ measurableSet_halfLineChart hc n measurableSet_Icc hsub

theorem arbitrary_cumulative_recovery (ν : ℝ → SignedMeasure ℝ)
    (hc : ∀ R S : ℝ, 0 ≤ R → 0 ≤ S →
      (ν R).restrict (Icc 0 R ∩ Icc 0 S) = (ν S).restrict (Icc 0 R ∩ Icc 0 S))
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ x in Iic t, jordanSign
      (glued_mutuallySingular halfLineChart (fun n => ν n) measurableSet_halfLineChart) x
        ∂variationGlue halfLineChart (fun n => ν n)) = ν t (Icc 0 t) := by
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hnat : Compatible halfLineChart (fun n => ν n) :=
    fun n m => hc n m (Nat.cast_nonneg n) (Nat.cast_nonneg m)
  rw [glued_cumulative_local_value _ hnat n t hn.le]
  have he := congrArg (fun s : SignedMeasure ℝ => s (Icc 0 t))
    (hc n t (Nat.cast_nonneg n) ht)
  dsimp only at he
  rw [VectorMeasure.restrict_apply _ (measurableSet_Icc.inter measurableSet_Icc) measurableSet_Icc,
    VectorMeasure.restrict_apply _ (measurableSet_Icc.inter measurableSet_Icc) measurableSet_Icc] at he
  have hi : Icc (0 : ℝ) t ∩ (Icc 0 (n : ℝ) ∩ Icc 0 t) = Icc 0 t := by
    apply inter_eq_left.mpr
    intro x hx
    exact ⟨⟨hx.1, hx.2.trans hn.le⟩, hx⟩
  rwa [hi] at he

theorem arbitrary_cauchy_cumulative (ν : ℝ → SignedMeasure ℝ)
    (hc : ∀ R S : ℝ, 0 ≤ R → 0 ≤ S →
      (ν R).restrict (Icc 0 R ∩ Icc 0 S) = (ν S).restrict (Icc 0 R ∩ Icc 0 S))
    {δ : ℝ} (hδ : 0 < δ)
    (hint : Integrable (fun s : ℝ => 1 / (1 + s))
      (variationGlue halfLineChart (fun n => ν n))) :
    (∫ s, 1 / (δ + s) ∂positiveGlue halfLineChart (fun n => ν n)) -
      (∫ s, 1 / (δ + s) ∂negativeGlue halfLineChart (fun n => ν n)) =
      ∫ t in Ici 0, ν t (Icc 0 t) / (δ + t)^2 := by
  have hnat : Compatible halfLineChart (fun n => ν n) :=
    fun n m => hc n m (Nat.cast_nonneg n) (Nat.cast_nonneg m)
  rw [glued_cauchy_cumulative _ hnat hδ hint]
  apply setIntegral_congr_fun measurableSet_Ici
  intro t ht
  dsimp only
  apply congrArg (fun z : ℝ => z / (δ + t)^2)
  change (∫ x in Iic t, jordanSign
    (glued_mutuallySingular halfLineChart (fun n => ν n) measurableSet_halfLineChart) x
      ∂variationGlue halfLineChart (fun n => ν n)) = ν t (Icc 0 t)
  exact arbitrary_cumulative_recovery ν hc t ht

end LeanVerification.LocalSigned
