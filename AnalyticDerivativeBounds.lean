import LeanVerification.WeightedAnalyticIntegral

/-!
# One common geometric bound for every mixed analytic derivative

The estimates follow from a genuine convergent multilinear series and its shifted
series. The constants do not depend on derivative order or direction vectors.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal

namespace LeanVerification.AnalyticDerivativeBounds

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem norm_iteratedFDeriv_le_coefficient
    {f : E → 𝕜} {p : FormalMultilinearSeries 𝕜 E 𝕜} {x : E} {R : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p x R) (n : ℕ) (v : Fin n → E) :
    ‖iteratedFDeriv 𝕜 n f x v‖ ≤ (n.factorial : ℝ) * ‖p n‖ * ∏ i, ‖v i‖ := by
  rw [hp.iteratedFDeriv_eq_sum_of_completeSpace v]
  apply (norm_sum_le _ _).trans
  calc
    ∑ σ : Equiv.Perm (Fin n), ‖p n (fun i => v (σ i))‖ ≤
        ∑ _σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro σ _
      simpa only [Equiv.prod_comp σ (fun i => ‖v i‖)] using
        (p n).le_opNorm (fun i => v (σ i))
    _ = (n.factorial : ℝ) * ‖p n‖ * ∏ i, ‖v i‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul, mul_assoc]

def shiftMajorant (p : FormalMultilinearSeries 𝕜 E 𝕜)
    (a : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  ∑' s : Σ l : ℕ, {s : Finset (Fin (n + l)) // s.card = l},
    ‖p (n + s.1)‖₊ * a ^ s.1

theorem summable_shiftMajorant (p : FormalMultilinearSeries 𝕜 E 𝕜)
    {a b : ℝ≥0} (hab : (a + b : ℝ≥0∞) < p.radius) :
    Summable (fun n => shiftMajorant p a n * b ^ n) := by
  simpa only [shiftMajorant, ← NNReal.tsum_mul_right] using
    (NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hab)).2

theorem nnnorm_changeOrigin_le_shiftMajorant (p : FormalMultilinearSeries 𝕜 E 𝕜)
    {a : ℝ≥0} (ha : (a : ℝ≥0∞) < p.radius) {z : E} (hz : ‖z‖₊ ≤ a) (n : ℕ) :
    ‖p.changeOrigin z n‖₊ ≤ shiftMajorant p a n := by
  have hzr : (‖z‖₊ : ℝ≥0∞) < p.radius :=
    (ENNReal.coe_le_coe.mpr hz).trans_lt ha
  refine (p.nnnorm_changeOrigin_le n hzr).trans ?_
  apply Summable.tsum_le_tsum
  · intro s
    exact mul_le_mul_left' (pow_le_pow_left' hz _) _
  · exact p.changeOriginSeries_summable_aux₂ hzr n
  · exact p.changeOriginSeries_summable_aux₂ ha n

/-- Analyticity gives one parameter neighborhood and one pair of constants
controlling every multilinear derivative, including all mixed directions. -/
theorem exists_uniform_factorial_derivative_bound {f : E → 𝕜} {x₀ : E}
    (hf : AnalyticAt 𝕜 f x₀) :
    ∃ ε C L : ℝ, 0 < ε ∧ 0 < C ∧ 0 < L ∧
      ∀ x ∈ ball x₀ ε, ∀ n : ℕ, ∀ v : Fin n → E,
        ‖iteratedFDeriv 𝕜 n f x v‖ ≤
          C * (n.factorial : ℝ) * L ^ n * ∏ i, ‖v i‖ := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨a, ha, haR⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hp.r_pos
  simp only [zero_add] at haR
  obtain ⟨b, hb, habR⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp haR
  have hab : (a + b : ℝ≥0∞) < p.radius := habR.trans_le hp.r_le
  have has : Summable (fun n => shiftMajorant p a n * b ^ n) := summable_shiftMajorant p hab
  let C : ℝ := (∑' n, shiftMajorant p a n * b ^ n : ℝ≥0) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hbR : 0 < (b : ℝ) := hb
  have hbound (n : ℕ) : (shiftMajorant p a n : ℝ) ≤ C * ((b : ℝ)⁻¹) ^ n := by
    have hn : shiftMajorant p a n * b ^ n ≤ ∑' k, shiftMajorant p a k * b ^ k :=
      has.le_tsum n (fun _ _ => zero_le _)
    have hnR : (shiftMajorant p a n : ℝ) * (b : ℝ) ^ n ≤ C := by
      have hn' : (shiftMajorant p a n : ℝ) * (b : ℝ) ^ n ≤
          ((∑' k, shiftMajorant p a k * b ^ k : ℝ≥0) : ℝ) := by exact_mod_cast hn
      dsimp only [C]
      linarith
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hbR n)]
    exact hnR
  refine ⟨a, C, (b : ℝ)⁻¹, ha, hC, inv_pos.mpr hbR, ?_⟩
  intro x hx n v
  have hxa : ‖x - x₀‖₊ ≤ a := by
    exact_mod_cast (mem_ball_iff_norm.mp hx).le
  have hxR : (‖x - x₀‖₊ : ℝ≥0∞) < R :=
    (ENNReal.coe_le_coe.mpr hxa).trans_lt haR
  have hpx : HasFPowerSeriesOnBall f (p.changeOrigin (x - x₀)) x
      (R - ‖x - x₀‖₊) := by
    have he : x₀ + (x - x₀) = x := by abel
    simpa only [he] using hp.changeOrigin hxR
  have hpbound : ‖p.changeOrigin (x - x₀) n‖ ≤ C * ((b : ℝ)⁻¹) ^ n := by
    have hm : ‖p.changeOrigin (x - x₀) n‖ ≤ (shiftMajorant p a n : ℝ) := by
      exact_mod_cast nnnorm_changeOrigin_le_shiftMajorant p (haR.trans_le hp.r_le) hxa n
    exact hm.trans (hbound n)
  apply (norm_iteratedFDeriv_le_coefficient hpx n v).trans
  calc
    (n.factorial : ℝ) * ‖p.changeOrigin (x - x₀) n‖ * ∏ i, ‖v i‖ ≤
        (n.factorial : ℝ) * (C * ((b : ℝ)⁻¹) ^ n) * ∏ i, ‖v i‖ := by
      gcongr
    _ = C * (n.factorial : ℝ) * ((b : ℝ)⁻¹) ^ n * ∏ i, ‖v i‖ := by ring

end LeanVerification.AnalyticDerivativeBounds
