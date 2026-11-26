import LeanVerification.Descartes
import LeanVerification.MomentVariation

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.ScalarSeries

theorem convergesOn_of_geometric_bound {a : ℕ → ℝ} {H M : ℝ}
    (hH : 0 < H) (hM : 0 ≤ M)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ M * H ^ (-(n : ℝ))) : ConvergesOn a H := by
  intro x hx
  have hq : 0 ≤ |x| / H := div_nonneg (abs_nonneg _) hH.le
  have hq1 : |x| / H < 1 := (div_lt_one hH).mpr hx
  apply Summable.of_norm_bounded (fun n => M * (|x| / H) ^ n)
    ((summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hq])).mul_left M)
  intro n
  calc
    ‖a n * x ^ n‖ = ‖a n‖ * |x| ^ n := by simp only [norm_mul, norm_pow, Real.norm_eq_abs]
    _ ≤ (M * H ^ (-(n : ℝ))) * |x| ^ n :=
      mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (abs_nonneg _) n)
    _ = M * (|x| / H) ^ n := by
      rw [Real.rpow_neg hH.le, Real.rpow_natCast, div_pow]
      ring

end LeanVerification.ScalarSeries

namespace LeanVerification.Stieltjes

theorem normalizedMoment_sequence_nonzero
    {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ} {n : ℕ}
    (d : MeasureSigns.BlockDecomposition μ f n) (hH : 0 < H) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    ∃ k : ℕ, normalizedMoment μ f (k : ℝ) ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply normalizedMoment_atMostZeros d hH hf hsupp hint
  refine ⟨fun i : Fin (n + 1) => (i.val : ℝ), ?_, ?_⟩
  · intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast hij
  · intro i
    refine ⟨?_, hn i.val⟩
    change (0 : ℝ) ≤ (i.val : ℝ)
    exact Nat.cast_nonneg _

theorem normalizedMomentSeries_converges
    {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ}
    (hH : 0 < H) (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    ScalarSeries.ConvergesOn (fun k : ℕ => normalizedMoment μ f (k : ℝ)) H := by
  apply ScalarSeries.convergesOn_of_geometric_bound hH
    (M := normalizedMomentMass μ f) ?_ ?_
  · exact div_nonneg (integral_nonneg fun _ => norm_nonneg _) Real.pi_pos.le
  · intro k
    exact normalizedMoment_bound hH (Nat.cast_nonneg _) hf hsupp hint

/-- Moment variation and the full convergent-series rule of signs combine
without assuming analyticity, nonvanishing, or a zero bound for the sum. -/
theorem normalizedMomentSeries_multiplicityBound
    {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ} {n : ℕ}
    (d : MeasureSigns.BlockDecomposition μ f n) (hH : 0 < H) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    AnalyticMultiplicity.MultiplicityBound n
      (ScalarSeries.sum (fun k : ℕ => normalizedMoment μ f (k : ℝ))) (Ioo 0 H) :=
  ScalarSeries.multiplicityBound_of_coefficient_sign_changes hH
    (normalizedMomentSeries_converges hH hf hsupp hint)
    (normalizedMoment_sequence_nonzero d hH hf hsupp hint)
    (normalizedMoment_sequence_signVariation d hH hf hsupp hint)

end LeanVerification.Stieltjes
