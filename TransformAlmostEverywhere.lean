import LeanVerification.SpectralTaylor

noncomputable section

open MeasureTheory Set Filter

namespace LeanVerification.MeasureSigns

def BlockDecomposition.congr_ae {μ : Measure ℝ} {f g : ℝ → ℝ} {n : ℕ}
    (d : BlockDecomposition μ f n) (he : f =ᵐ[μ] g) : BlockDecomposition μ g n where
  blocks := d.blocks
  measurable := d.measurable
  disjoint := d.disjoint
  nonzero := by
    intro i hn
    apply d.nonzero i
    filter_upwards [he, hn] with x hx hi
    intro hxi
    rw [hx]
    exact hi hxi
  cover := by
    filter_upwards [he, d.cover] with x hx hc
    rw [← hx]
    exact hc
  separators := d.separators
  separator_nonneg := d.separator_nonneg
  lower := d.lower
  upper := d.upper
  orientation := d.orientation
  orientation_ne_zero := d.orientation_ne_zero
  signs := by
    intro i
    filter_upwards [he, d.signs i] with x hx hs
    rw [← hx]
    exact hs

theorem cauchy_atMostZeros_ae {μ : Measure ℝ} {f : ℝ → ℝ} {β : ℝ} {n : ℕ}
    (d : BlockDecomposition μ f n) (hβ : 0 < β) (hf : AEStronglyMeasurable f μ)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    FiniteZeroCounting.AtMostZeros n (Cauchy.transform μ f β) (Ioi 0) := by
  let g := hf.aemeasurable.mk f
  have hg : Measurable g := hf.aemeasurable.measurable_mk
  have he : f =ᵐ[μ] g := hf.aemeasurable.ae_eq_mk
  have hi : Integrable (fun t => g t * (1 + t) ^ (-β)) μ := by
    apply hint.congr
    filter_upwards [he] with t ht
    rw [ht]
  have hc : Cauchy.transform μ f β = Cauchy.transform μ g β := by
    funext δ
    apply integral_congr_ae
    filter_upwards [he] with t ht
    rw [ht]
  rw [hc]
  exact cauchy_atMostZeros (d.congr_ae he) hβ hg hsupp hi

end LeanVerification.MeasureSigns

namespace LeanVerification.Stieltjes

theorem normalizedMoment_congr_ae {μ : Measure ℝ} {f g : ℝ → ℝ} (he : f =ᵐ[μ] g) :
    normalizedMoment μ f = normalizedMoment μ g := by
  funext r
  unfold normalizedMoment weightedMoment
  congr 1
  apply integral_congr_ae
  filter_upwards [he] with t ht
  rw [ht]

theorem normalizedMoment_atMostZeros_ae {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ} {n : ℕ}
    (d : MeasureSigns.BlockDecomposition μ f n) (hH : 0 < H)
    (hf : AEStronglyMeasurable f μ) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    FiniteZeroCounting.AtMostZeros n (normalizedMoment μ f) (Ici 0) := by
  let g := hf.aemeasurable.mk f
  have hg : Measurable g := hf.aemeasurable.measurable_mk
  have he : f =ᵐ[μ] g := hf.aemeasurable.ae_eq_mk
  have hi : Integrable (fun t => g t * t ^ (-(3 : ℝ) / 2)) μ := by
    apply hint.congr
    filter_upwards [he] with t ht
    rw [ht]
  rw [normalizedMoment_congr_ae he]
  exact normalizedMoment_atMostZeros (d.congr_ae he) hH hg hsupp hi

theorem normalizedMoment_sequence_signVariation_ae
    {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ} {n : ℕ}
    (d : MeasureSigns.BlockDecomposition μ f n) (hH : 0 < H)
    (hf : AEStronglyMeasurable f μ) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    FiniteZeroCounting.AtMostSequenceSignChanges n
      (fun k : ℕ => normalizedMoment μ f (k : ℝ)) := by
  let g := hf.aemeasurable.mk f
  have hg : Measurable g := hf.aemeasurable.measurable_mk
  have he : f =ᵐ[μ] g := hf.aemeasurable.ae_eq_mk
  have hi : Integrable (fun t => g t * t ^ (-(3 : ℝ) / 2)) μ := by
    apply hint.congr
    filter_upwards [he] with t ht
    rw [ht]
  simp only [normalizedMoment_congr_ae he]
  exact normalizedMoment_sequence_signVariation (d.congr_ae he) hH hg hsupp hi

/-- A nonzero moment occurs beyond every finite index, as a consequence
of the proved continuous-exponent zero bound. -/
theorem normalizedMoment_sequence_nonzero_tail_ae
    {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ} {n : ℕ}
    (d : MeasureSigns.BlockDecomposition μ f n) (hH : 0 < H)
    (hf : AEStronglyMeasurable f μ) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ normalizedMoment μ f (k : ℝ) ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply normalizedMoment_atMostZeros_ae d hH hf hsupp hint
  refine ⟨fun i : Fin (n + 1) => ((i.val + N : ℕ) : ℝ), ?_, ?_⟩
  · intro i j hij
    change ((i.val + N : ℕ) : ℝ) < ((j.val + N : ℕ) : ℝ)
    exact_mod_cast Nat.add_lt_add_right (show i.val < j.val from hij) N
  · intro i
    refine ⟨?_, hn (i.val + N) (Nat.le_add_left _ _)⟩
    change (0 : ℝ) ≤ ((i.val + N : ℕ) : ℝ)
    exact Nat.cast_nonneg _

end LeanVerification.Stieltjes
