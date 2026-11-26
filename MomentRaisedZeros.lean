import LeanVerification.TransformAlmostEverywhere
import LeanVerification.EulerSeries

noncomputable section

open MeasureTheory Set Filter

namespace LeanVerification.SequenceSigns

theorem atMost_mul_nonnegative {a p : ℕ → ℝ} {n : ℕ}
    (h : FiniteZeroCounting.AtMostSequenceSignChanges n a) (hp : ∀ k, 0 ≤ p k) :
    FiniteZeroCounting.AtMostSequenceSignChanges n (fun k => p k * a k) := by
  intro ⟨k, hk, hn, hs⟩
  have hpp : ∀ i, 0 < p (k i) := by
    intro i
    exact lt_of_le_of_ne (hp _) (Ne.symm (mul_ne_zero_iff.mp (hn i)).1)
  apply h
  refine ⟨k, hk, fun i => (mul_ne_zero_iff.mp (hn i)).2, ?_⟩
  intro i
  have he : p (k i.castSucc) * a (k i.castSucc) *
      (p (k i.succ) * a (k i.succ)) =
      (p (k i.castSucc) * p (k i.succ)) * (a (k i.castSucc) * a (k i.succ)) := by ring
  have hh := hs i
  rw [he] at hh
  exact neg_of_mul_neg_right hh (mul_pos (hpp _) (hpp _)).le

end LeanVerification.SequenceSigns

namespace LeanVerification.Stieltjes

/-- The actual raised moment series is nonzero and satisfies the full
analytic multiplicity bound. Its input may be the actual AE-measurable
bank density together with signed atoms. -/
theorem normalizedMomentRaised_multiplicityBound
    {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ} {n : ℕ}
    (d : MeasureSigns.BlockDecomposition μ f n) (hH : 0 < H)
    (hf : AEStronglyMeasurable f μ) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    AnalyticMultiplicity.MultiplicityBound n
      (ScalarSeries.sum (EulerSeries.raisedCoefficient
        (fun k : ℕ => normalizedMoment μ f (k : ℝ)))) (Ioo 0 H) := by
  have hc := EulerSeries.raised_converges hH (SpectralTaylor.moment_converges hH hsupp hint)
  have hp : ∀ k : ℕ, 0 ≤ (k : ℝ) * (k + 1) * (k + 2) * (k + (1 : ℝ) / 2) := by
    intro k
    positivity
  have hsv := SequenceSigns.atMost_mul_nonnegative
    (normalizedMoment_sequence_signVariation_ae d hH hf hsupp hint) hp
  have hn : ∃ k : ℕ, EulerSeries.raisedCoefficient
      (fun k : ℕ => normalizedMoment μ f (k : ℝ)) k ≠ 0 := by
    obtain ⟨k, hk, hm⟩ := normalizedMoment_sequence_nonzero_tail_ae d hH hf hsupp hint 1
    refine ⟨k, ?_⟩
    have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hpos : 0 < (k : ℝ) * (k + 1) * (k + 2) * (k + (1 : ℝ) / 2) := by positivity
    exact mul_ne_zero hpos.ne' hm
  exact ScalarSeries.multiplicityBound_of_coefficient_sign_changes hH hc hn hsv

end LeanVerification.Stieltjes
