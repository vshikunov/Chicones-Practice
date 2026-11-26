import LeanVerification.OrderedSignBlocks
import LeanVerification.LaplaceZeroCount
import LeanVerification.MomentRegularity

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace LeanVerification.MeasureSigns

theorem separators_ge_of_support {μ : Measure ℝ} {f : ℝ → ℝ} {n : ℕ} {H : ℝ}
    (d : BlockDecomposition μ f n) (hsupp : ∀ᵐ t ∂μ, H ≤ t) :
    ∀ j, H ≤ d.separators j := by
  intro j
  by_contra hn
  apply d.nonzero 0
  filter_upwards [hsupp] with t ht
  intro hB
  have hle := d.upper 0 j (Nat.zero_le _) t hB
  exact (not_le_of_gt (lt_of_not_ge hn) (ht.trans hle)).elim

/-- A positive weight and a strictly increasing coordinate preserve the
separator sign certificate, without discarding transition atoms. -/
theorem mapped_factoredInput_nonnegative
    {μ : Measure ℝ} {f w a : ℝ → ℝ} {n : ℕ} {H : ℝ}
    (d : BlockDecomposition μ f n) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hw : StrictMonoOn w (Ici H)) (ha : ∀ᵐ t ∂μ, 0 < a t) :
    ∀ᵐ t ∂μ, 0 ≤ Laplace.factoredInput w (List.ofFn fun j => w (d.separators j))
      (fun t => a t * (d.orientation * f t)) t := by
  have hc := separators_ge_of_support d hsupp
  have hall : ∀ᵐ t ∂μ, ∀ i, t ∈ d.blocks i →
      0 ≤ blockOrientation i * (d.orientation * f t) := eventually_all.mpr d.signs
  filter_upwards [hsupp, ha, d.cover, hall] with t ht hat hcover hsign
  simp only [Laplace.factoredInput_eq_product, List.map_ofFn, Function.comp_def, List.prod_ofFn]
  by_cases hft : f t = 0
  · simp [hft]
  obtain ⟨i, hi⟩ := hcover hft
  have hfac : ∀ j : Fin n, 0 ≤ separatorSign i j * (w t - w (d.separators j)) := by
    intro j
    unfold separatorSign
    split_ifs with hj
    · simpa only [one_mul] using sub_nonneg.mpr
        (hw.monotoneOn (hc j) ht (d.lower i j hj t hi))
    · have hh := hw.monotoneOn ht (hc j) (d.upper i j (le_of_not_gt hj) t hi)
      simp only [neg_one_mul]
      linarith
  have hprod : 0 ≤ ∏ j : Fin n, separatorSign i j * (w t - w (d.separators j)) :=
    Finset.prod_nonneg fun j _ => hfac j
  have hp := mul_nonneg hprod (mul_nonneg hat.le (hsign i hi))
  rw [Finset.prod_mul_distrib] at hp
  change 0 ≤ (blockOrientation i * ∏ j : Fin n, (w t - w (d.separators j))) *
    (a t * (blockOrientation i * (d.orientation * f t))) at hp
  have he : (blockOrientation i * ∏ j : Fin n, (w t - w (d.separators j))) *
      (a t * (blockOrientation i * (d.orientation * f t))) =
      (∏ j : Fin n, (w t - w (d.separators j))) * (a t * (d.orientation * f t)) := by
    calc
      _ = (blockOrientation i * blockOrientation i) *
          ((∏ j : Fin n, (w t - w (d.separators j))) * (a t * (d.orientation * f t))) := by ring
      _ = _ := by rw [blockOrientation_square, one_mul]
  rwa [he] at hp

theorem mapped_factoredInput_nonzero
    {μ : Measure ℝ} {f w a : ℝ → ℝ} {n : ℕ} {H : ℝ}
    (d : BlockDecomposition μ f n) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hw : StrictMonoOn w (Ici H)) (ha : ∀ᵐ t ∂μ, 0 < a t) :
    ¬Laplace.factoredInput w (List.ofFn fun j => w (d.separators j))
      (fun t => a t * (d.orientation * f t)) =ᵐ[μ] 0 := by
  classical
  intro hz
  have hc := separators_ge_of_support d hsupp
  apply factoredDensity_nonzero d
  filter_upwards [hsupp, ha, hz] with t ht hat hzt
  simp only [Cauchy.factoredDensity_eq_product, List.map_ofFn,
    Function.comp_def, List.prod_ofFn, Pi.zero_apply]
  by_cases hft : f t = 0
  · simp [hft]
  have hp : (∏ j : Fin n, (w t - w (d.separators j))) = 0 := by
    simp only [Laplace.factoredInput_eq_product, List.map_ofFn,
      Function.comp_def, List.prod_ofFn, Pi.zero_apply] at hzt
    exact (mul_eq_zero.mp hzt).resolve_right
      (mul_ne_zero hat.ne' (mul_ne_zero d.orientation_ne_zero hft))
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
  have htj : t = d.separators j := hw.injOn ht (hc j) (sub_eq_zero.mp hj)
  have hpz : (∏ j : Fin n, (t - d.separators j)) = 0 := by
    apply Finset.prod_eq_zero_iff.mpr
    exact ⟨j, Finset.mem_univ _, sub_eq_zero.mpr htj⟩
  rw [hpz, zero_mul]

end LeanVerification.MeasureSigns

namespace LeanVerification.Stieltjes

def logHeight (H t : ℝ) : ℝ := Real.log t - Real.log H

theorem laplace_eq_weightedMoment {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ}
    (hH : 0 < H) (hsupp : ∀ᵐ t ∂μ, H ≤ t) (q s : ℝ) :
    Laplace.transform μ (logHeight H) (fun t => t ^ (-(3 : ℝ) / 2) * (q * f t)) s =
      (q * H ^ s) * weightedMoment μ f s := by
  unfold Laplace.transform weightedMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hsupp] with t ht
  have hp : 0 < t := hH.trans_le ht
  have he : -s * logHeight H t = Real.log H * s + Real.log t * (-s) := by
    dsimp [logHeight]
    ring
  rw [he, Real.exp_add, ← Real.rpow_def_of_pos hH, ← Real.rpow_def_of_pos hp,
    show -s - (3 : ℝ) / 2 = -(3 : ℝ) / 2 + (-s) by ring, Real.rpow_add hp]
  ring

/-- The actual moment transform has at most the input's ordered-block
alternations, including a possible zero at exponent zero. -/
theorem weightedMoment_atMostZeros {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ} {n : ℕ}
    (d : MeasureSigns.BlockDecomposition μ f n) (hH : 0 < H) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    FiniteZeroCounting.AtMostZeros n (weightedMoment μ f) (Ici 0) := by
  have hw : Measurable (logHeight H) := Real.measurable_log.sub_const _
  have hwm : StrictMonoOn (logHeight H) (Ici H) := by
    intro x hx y hy hxy
    exact sub_lt_sub_right (Real.log_lt_log (hH.trans_le hx) hxy) _
  have hwp : ∀ᵐ t ∂μ, 0 ≤ logHeight H t := by
    filter_upwards [hsupp] with t ht
    exact sub_nonneg.mpr (Real.log_le_log hH ht)
  have ha : ∀ᵐ t ∂μ, 0 < t ^ (-(3 : ℝ) / 2) :=
    hsupp.mono fun t ht => Real.rpow_pos_of_pos (hH.trans_le ht) _
  have hgf : Measurable (fun t => t ^ (-(3 : ℝ) / 2) * (d.orientation * f t)) :=
    (measurable_id.pow_const _).mul (hf.const_mul _)
  have hgi : Integrable (fun t => t ^ (-(3 : ℝ) / 2) * (d.orientation * f t)) μ := by
    apply (hint.const_mul d.orientation).congr
    filter_upwards [] with t
    ring
  have hb := Laplace.atMostZeros_Ici_of_factor_certificate
    (List.ofFn fun j => logHeight H (d.separators j)) hw hgf hwp hgi
    (MeasureSigns.mapped_factoredInput_nonnegative d hsupp hwm ha)
    (MeasureSigns.mapped_factoredInput_nonzero d hsupp hwm ha)
  have he : Laplace.transform μ (logHeight H)
      (fun t => t ^ (-(3 : ℝ) / 2) * (d.orientation * f t)) =
      fun s => (d.orientation * H ^ s) * weightedMoment μ f s := by
    funext s
    exact laplace_eq_weightedMoment hH hsupp d.orientation s
  rw [List.length_ofFn, he] at hb
  exact (FiniteZeroCounting.atMostZeros_mul_iff fun s _ =>
    mul_ne_zero d.orientation_ne_zero (Real.rpow_pos_of_pos hH s).ne').mp hb

theorem normalizedMoment_atMostZeros {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ} {n : ℕ}
    (d : MeasureSigns.BlockDecomposition μ f n) (hH : 0 < H) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    FiniteZeroCounting.AtMostZeros n (normalizedMoment μ f) (Ici 0) := by
  apply FiniteZeroCounting.atMostZeros_of_same_zeros
    (f := weightedMoment μ f) ?_ (weightedMoment_atMostZeros d hH hf hsupp hint)
  intro s hs
  simp only [normalizedMoment, div_eq_zero_iff, Real.pi_ne_zero, or_false]

theorem normalizedMoment_nonvanishing {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ} {n : ℕ}
    (d : MeasureSigns.BlockDecomposition μ f n) (hH : 0 < H) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    ∃ s > 0, normalizedMoment μ f s ≠ 0 := by
  exact FiniteZeroCounting.exists_nonzero_Ioi
    ((normalizedMoment_atMostZeros d hH hf hsupp hint).mono Ioi_subset_Ici_self)

theorem normalizedMoment_sequence_signVariation
    {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ} {n : ℕ}
    (d : MeasureSigns.BlockDecomposition μ f n) (hH : 0 < H) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    FiniteZeroCounting.AtMostSequenceSignChanges n (fun k => normalizedMoment μ f (k : ℝ)) :=
  FiniteZeroCounting.sequence_signVariation_of_zero_bound
    (continuousOn_normalizedMoment hH hf hsupp hint)
    (normalizedMoment_atMostZeros d hH hf hsupp hint)

end LeanVerification.Stieltjes
