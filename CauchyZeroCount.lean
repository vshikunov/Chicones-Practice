import LeanVerification.CauchyDifferentiation
import LeanVerification.FiniteZeroCounting

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.Cauchy

/-- Multiplying the input successively by the separator factors. Repeated
separators retain their multiplicity and annihilate atoms at that location. -/
def factoredDensity : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | c :: cs, f => factoredDensity cs (factorDensity c f)

theorem factoredDensity_eq_product (cs : List ℝ) (f : ℝ → ℝ) (t : ℝ) :
    factoredDensity cs f t = (cs.map (fun c => t - c)).prod * f t := by
  induction cs generalizing f with
  | nil => simp [factoredDensity]
  | cons c cs ih =>
      simp only [factoredDensity, ih, List.map_cons, List.prod_cons, factorDensity]
      ring

theorem transform_pos_of_nonnegative {μ : Measure ℝ} {f : ℝ → ℝ} {β δ : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 < δ) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ)
    (hsign : ∀ᵐ t ∂μ, 0 ≤ f t) (hnz : ¬f =ᵐ[μ] 0) :
    0 < transform μ f β δ := by
  have hi := integrable_transform hβ hδ hf hsupp hint
  have hn : ∀ᵐ t ∂μ, 0 ≤ f t * (δ + t) ^ (-β) := by
    filter_upwards [hsupp, hsign] with t ht hft
    exact mul_nonneg hft (Real.rpow_nonneg (by linarith) _)
  have hne : (∫ t, f t * (δ + t) ^ (-β) ∂μ) ≠ 0 := by
    intro hz
    have he := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
    apply hnz
    filter_upwards [he, hsupp] with t ht hs
    exact (mul_eq_zero.mp ht).resolve_right
      (Real.rpow_pos_of_pos (by linarith : 0 < δ + t) (-β)).ne'
  exact lt_of_le_of_ne (integral_nonneg_of_ae hn) hne.symm

/-- A finite algebraic sign certificate gives the complete distinct-zero
bound for the actual generalized Cauchy transform. Weighted integrability
and differentiation are discharged at every reduction step. -/
theorem atMostZeros_of_factor_certificate {μ : Measure ℝ} {f : ℝ → ℝ} {β : ℝ}
    (cs : List ℝ) (hcs : ∀ c ∈ cs, 0 ≤ c) (hβ : 0 < β)
    (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ)
    (hsign : ∀ᵐ t ∂μ, 0 ≤ factoredDensity cs f t)
    (hnz : ¬factoredDensity cs f =ᵐ[μ] 0) :
    FiniteZeroCounting.AtMostZeros cs.length (transform μ f β) (Ioi 0) := by
  induction cs generalizing f β with
  | nil =>
      apply FiniteZeroCounting.atMostZeros_zero_iff.mpr
      intro δ hδ
      exact (transform_pos_of_nonnegative hβ.le hδ hf hsupp hint hsign hnz).ne'
  | cons c cs ih =>
      have hc : 0 ≤ c := hcs c (by simp)
      have htail : ∀ d ∈ cs, 0 ≤ d := fun d hd => hcs d (by simp [hd])
      have hnew := ih htail (show 0 < β + 1 by linarith)
        ((measurable_id.sub_const c).mul hf)
        (integrable_factorDensity c hf hsupp hint) hsign hnz
      let N : ℝ → ℝ := fun δ => (δ + c) ^ β * transform μ f β δ
      have hd : ∀ δ ∈ Ioi (0 : ℝ),
          HasDerivAt N
            (β * (δ + c) ^ (β - 1) * transform μ (factorDensity c f) (β + 1) δ) δ :=
        fun δ hδ => hasDerivAt_normalized_transform hβ hδ hc hf hsupp hint
      have he : ∀ δ ∈ Ioi (0 : ℝ),
          transform μ (factorDensity c f) (β + 1) δ = 0 ↔ deriv N δ = 0 := by
        intro δ hδ
        change 0 < δ at hδ
        rw [(hd δ hδ).deriv]
        have hfac : β * (δ + c) ^ (β - 1) ≠ 0 :=
          mul_ne_zero hβ.ne' (Real.rpow_pos_of_pos (by linarith : 0 < δ + c) _).ne'
        simp only [mul_eq_zero, hfac, false_or]
      have hdn : FiniteZeroCounting.AtMostZeros cs.length (deriv N) (Ioi 0) :=
        FiniteZeroCounting.atMostZeros_of_same_zeros he hnew
      have hN := FiniteZeroCounting.atMostZeros_of_derivative (convex_Ioi (0 : ℝ))
        (fun δ hδ => (hd δ hδ).continuousAt.continuousWithinAt) hdn
      have hw : ∀ δ ∈ Ioi (0 : ℝ), (δ + c) ^ β ≠ 0 := by
        intro δ hδ
        change 0 < δ at hδ
        exact (Real.rpow_pos_of_pos (by linarith : 0 < δ + c) β).ne'
      exact (FiniteZeroCounting.atMostZeros_mul_iff hw).mp hN

theorem transform_not_identically_zero_of_factor_certificate
    {μ : Measure ℝ} {f : ℝ → ℝ} {β : ℝ}
    (cs : List ℝ) (hcs : ∀ c ∈ cs, 0 ≤ c) (hβ : 0 < β)
    (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ)
    (hsign : ∀ᵐ t ∂μ, 0 ≤ factoredDensity cs f t)
    (hnz : ¬factoredDensity cs f =ᵐ[μ] 0) :
    ∃ δ > 0, transform μ f β δ ≠ 0 :=
  FiniteZeroCounting.exists_nonzero_Ioi
    (atMostZeros_of_factor_certificate cs hcs hβ hf hsupp hint hsign hnz)

end LeanVerification.Cauchy
