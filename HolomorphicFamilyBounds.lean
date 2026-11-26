import LeanVerification.HolomorphicPolydiscFamily
import LeanVerification.BanachAnalyticBounds

/-!
# Uniform mixed derivative bounds for weighted compact holomorphic families

Scalar fiber holomorphy and joint continuity give a common neighborhood and
constants controlling every mixed derivative, uniformly over the compact fiber.
The same bounds pass to an arbitrary integrable complex weighted integral.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex ContinuousMap
open scoped Topology ENNReal NNReal

namespace LeanVerification.PolydiscCauchy

set_option maxHeartbeats 1000000

variable {n : ℕ} {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- One neighborhood and constants control every ordered mixed derivative,
uniformly over the compact integration set. The bound uses total-order `k!`.
No coefficient estimates are hypotheses. -/
theorem uniform_holomorphic_family_derivative_bounds
    {f : (Fin n → ℂ) → C(K, ℂ)} {Q : Set (Fin n → ℂ)} (hQ : IsOpen Q)
    (hc : ContinuousOn (fun p : (Fin n → ℂ) × K => f p.1 p.2) (Q ×ˢ univ))
    (hf : ∀ t : K, AnalyticOnNhd ℂ (fun q => f q t) Q)
    {z : Fin n → ℂ} (hz : z ∈ Q) :
    ∃ ε C L : ℝ, 0 < ε ∧ 0 < C ∧ 0 < L ∧ ball z ε ⊆ Q ∧
      ∀ q ∈ ball z ε, ∀ k : ℕ, ∀ v : Fin k → (Fin n → ℂ), ∀ t : K,
        ‖iteratedFDeriv ℂ k (fun w => f w t) q v‖ ≤
          C * (k.factorial : ℝ) * L ^ k * ∏ i, ‖v i‖ := by
  have ha := analyticAt_continuousFamily_of_scalar hQ hc hf hz
  obtain ⟨ε, C, L, hε, hC, hL, hb⟩ :=
    BanachAnalyticBounds.exists_uniform_factorial_derivative_bound ha
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds hz)
  refine ⟨min ε δ, C, L, lt_min hε hδ, hC, hL, ?_, ?_⟩
  · exact (ball_subset_ball (min_le_right _ _)).trans hsub
  · intro q hq k v t
    have hqε : q ∈ ball z ε := (ball_subset_ball (min_le_left _ _)) hq
    have hqQ : q ∈ Q := hsub ((ball_subset_ball (min_le_right _ _)) hq)
    have haq := analyticAt_continuousFamily_of_scalar hQ hc hf hqQ
    have he := (ContinuousMap.evalCLM ℂ t).iteratedFDeriv_comp_left
      (haq.contDiffAt : ContDiffAt ℂ (k : WithTop ℕ∞) f q) (le_refl (k : WithTop ℕ∞))
    have hev := congrArg (fun p : (Fin n → ℂ)[×k]→L[ℂ] ℂ => p v) he
    change iteratedFDeriv ℂ k (fun w => f w t) q v =
      iteratedFDeriv ℂ k f q v t at hev
    rw [hev]
    exact ((iteratedFDeriv ℂ k f q v).norm_coe_le_norm t).trans (hb q hqε k v)

section Weighted
variable [MeasurableSpace K] [BorelSpace K] {μ : Measure K} {ω : K → ℂ}

/-- All derivative identities and estimates hold on one parameter neighborhood.
The integral estimate retains the explicit `L¹` norm of the weight. -/
theorem uniform_weighted_holomorphic_derivative_bounds
    {f : (Fin n → ℂ) → C(K, ℂ)} {Q : Set (Fin n → ℂ)} (hQ : IsOpen Q)
    (hc : ContinuousOn (fun p : (Fin n → ℂ) × K => f p.1 p.2) (Q ×ˢ univ))
    (hf : ∀ t : K, AnalyticOnNhd ℂ (fun q => f q t) Q)
    (hω : Integrable ω μ) {z : Fin n → ℂ} (hz : z ∈ Q) :
    ∃ ε C L : ℝ, 0 < ε ∧ 0 < C ∧ 0 < L ∧ ball z ε ⊆ Q ∧
      ∀ q ∈ ball z ε, ∀ k : ℕ, ∀ v : Fin k → (Fin n → ℂ),
        Integrable (fun t => ω t * iteratedFDeriv ℂ k (fun w => f w t) q v) μ ∧
        iteratedFDeriv ℂ k (fun w => ∫ t, ω t * f w t ∂μ) q v =
          ∫ t, ω t * iteratedFDeriv ℂ k (fun w => f w t) q v ∂μ ∧
        (∀ t : K, ‖iteratedFDeriv ℂ k (fun w => f w t) q v‖ ≤
          C * (k.factorial : ℝ) * L ^ k * ∏ i, ‖v i‖) ∧
        ‖iteratedFDeriv ℂ k (fun w => ∫ t, ω t * f w t ∂μ) q v‖ ≤
          (∫ t, ‖ω t‖ ∂μ) * (C * (k.factorial : ℝ) * L ^ k * ∏ i, ‖v i‖) := by
  obtain ⟨ε, C, L, hε, hC, hL, hsub, hb⟩ :=
    uniform_holomorphic_family_derivative_bounds hQ hc hf hz
  refine ⟨ε, C, L, hε, hC, hL, hsub, ?_⟩
  intro q hq k v
  obtain ⟨hi, he⟩ := all_derivatives_weighted_holomorphicIntegral_of_joint hQ hc hf hω (hsub hq) k v
  refine ⟨hi, he, hb q hq k v, ?_⟩
  rw [he]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_mul_const]
  apply integral_mono_ae hi.norm (hω.norm.mul_const _)
  filter_upwards [] with t
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb q hq k v t) (norm_nonneg (ω t))

end Weighted
end LeanVerification.PolydiscCauchy
