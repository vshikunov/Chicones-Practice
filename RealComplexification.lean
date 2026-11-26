import LeanVerification.HolomorphicPolydiscFamily

/-!
# Actual holomorphic extensions of finite-dimensional real analytic germs

Real continuous multilinear coefficients extend by their coordinate expansion.
A dimension-dependent geometric bound proves a positive complex convergence
radius; the extension agrees with the original real series.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology BigOperators ENNReal NNReal

namespace LeanVerification.RealComplexification

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

abbrev RVec (m : ℕ) := Fin m → ℝ
abbrev CVec (m : ℕ) := Fin m → ℂ

variable {m k : ℕ}

def embed (x : RVec m) : CVec m := fun i => (x i : ℂ)

@[simp] theorem embed_apply (x : RVec m) (i : Fin m) : embed x i = (x i : ℂ) := rfl

@[simp] theorem embed_sub (x y : RVec m) : embed (x-y) = embed x-embed y := by
  ext i
  exact Complex.ofReal_sub _ _

@[simp] theorem norm_embed (x : RVec m) : ‖embed x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    rw [embed_apply, Complex.norm_real]
    exact norm_le_pi_norm x i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (embed x))).mpr
    intro i
    rw [← Complex.norm_real]
    exact norm_le_pi_norm (embed x) i

@[simp] theorem nnnorm_embed (x : RVec m) : ‖embed x‖₊ = ‖x‖₊ := by
  apply Subtype.ext
  exact norm_embed x

def embedCLM : RVec m →L[ℝ] CVec m :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

@[simp] theorem embedCLM_apply (x : RVec m) : embedCLM x = embed x := rfl

def coordinateMonomial (a : Fin k → Fin m) : (CVec m)[×k]→L[ℂ] ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin k) ℂ).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (a i))

@[simp] theorem coordinateMonomial_apply (a : Fin k → Fin m) (v : Fin k → CVec m) :
    coordinateMonomial a v = ∏ i, v i (a i) := rfl

theorem norm_coordinateMonomial_le (a : Fin k → Fin m) : ‖coordinateMonomial a‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro v
  rw [coordinateMonomial_apply, norm_prod, one_mul]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => norm_le_pi_norm (v i) (a i))

def coefficient (p : (RVec m)[×k]→L[ℝ] ℂ) : (CVec m)[×k]→L[ℂ] ℂ :=
  ∑ a : Fin k → Fin m, p (fun i => Pi.single (a i) 1) • coordinateMonomial a

theorem norm_coefficient_le (p : (RVec m)[×k]→L[ℝ] ℂ) :
    ‖coefficient p‖ ≤ (m : ℝ)^k * ‖p‖ := by
  apply (norm_sum_le (Finset.univ) (fun a : Fin k → Fin m =>
    p (fun i => Pi.single (a i) 1) • coordinateMonomial a)).trans
  calc
    ∑ a : Fin k → Fin m, ‖p (fun i => Pi.single (a i) 1) • coordinateMonomial a‖ ≤
        ∑ _a : Fin k → Fin m, ‖p‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul (p (fun i => Pi.single (a i) 1)) (coordinateMonomial a)]
      have hp : ‖p (fun i => Pi.single (a i) 1)‖ ≤ ‖p‖ := by
        simpa only [Pi.norm_single, norm_one, Finset.prod_const_one, mul_one] using
          p.le_opNorm (fun i => Pi.single (a i) 1)
      exact (mul_le_mul_of_nonneg_left (norm_coordinateMonomial_le a) (norm_nonneg _)).trans
        (by simpa only [mul_one] using hp)
    _ = (m : ℝ)^k * ‖p‖ := by simp

theorem real_coordinate_expansion (x : RVec m) :
    (∑ j : Fin m, x j • (Pi.single j (1 : ℝ) : RVec m)) = x := by
  have he (j : Fin m) : x j • (Pi.single j (1 : ℝ) : RVec m) = Pi.single j (x j) := by
    ext i
    by_cases hi : i=j
    · subst i; simp
    · simp [Pi.single_eq_of_ne hi]
  simp only [he]
  exact Finset.univ_sum_single x

theorem coefficient_apply_embed (p : (RVec m)[×k]→L[ℝ] ℂ) (v : Fin k → RVec m) :
    coefficient p (fun i => embed (v i)) = p v := by
  have he := p.map_sum (fun i j => v i j • (Pi.single j (1 : ℝ) : RVec m))
  simp only [real_coordinate_expansion] at he
  rw [he]
  simp only [coefficient, ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    coordinateMonomial_apply, embed_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [p.map_smul_univ]
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_prod]
  ring

def complexSeries (p : FormalMultilinearSeries ℝ (RVec m) ℂ) :
    FormalMultilinearSeries ℂ (CVec m) ℂ := fun k => coefficient (p k)

theorem complexSeries_radius_pos {p : FormalMultilinearSeries ℝ (RVec m) ℂ}
    (hp : 0 < p.radius) : 0 < (complexSeries p).radius := by
  obtain ⟨C, L, hC, hL, hbound⟩ := p.le_mul_pow_of_radius_pos hp
  let B : ℝ := max 1 ((m : ℝ)*L)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let r : ℝ≥0 := ⟨B⁻¹, (inv_pos.mpr hB).le⟩
  have hr : 0 < r := inv_pos.mpr hB
  apply (ENNReal.coe_pos.mpr hr).trans_le
  apply (complexSeries p).le_radius_of_bound C
  intro k
  have hk : ‖complexSeries p k‖ ≤ C * B^k := by
    calc
      ‖complexSeries p k‖ ≤ (m : ℝ)^k * ‖p k‖ := norm_coefficient_le (p k)
      _ ≤ (m : ℝ)^k * (C*L^k) := mul_le_mul_of_nonneg_left (hbound k) (by positivity)
      _ = C*((m : ℝ)*L)^k := by rw [mul_pow]; ring
      _ ≤ C*B^k := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (le_max_right _ _) k) hC.le
  calc
    ‖complexSeries p k‖ * (r : ℝ)^k ≤ C*B^k*(B⁻¹)^k :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = C := by rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hB.ne', one_pow, mul_one]

/-- Every finite-dimensional real analytic germ, including complex-valued
real analytic functions, has an actual local holomorphic extension. -/
theorem exists_local_holomorphic_extension
    {f : RVec m → ℂ} {x₀ : RVec m} (hf : AnalyticAt ℝ f x₀) :
    ∃ G : CVec m → ℂ, ∃ ε : ℝ, 0 < ε ∧
      AnalyticOnNhd ℂ G (ball (embed x₀) ε) ∧
      ∀ x ∈ ball x₀ ε, G (embed x) = f x := by
  obtain ⟨p, R, hp⟩ := hf
  let q := complexSeries p
  have hq : 0 < q.radius := complexSeries_radius_pos hp.radius_pos
  obtain ⟨r, hr, hrR⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp (lt_min hp.r_pos hq)
  simp only [zero_add] at hrR
  let G : CVec m → ℂ := fun z => q.sum (z - embed x₀)
  refine ⟨G, r, hr, ?_, ?_⟩
  · intro z hz
    have hzq : z - embed x₀ ∈ EMetric.ball 0 q.radius := by
      rw [mem_emetric_ball_zero_iff, enorm_eq_nnnorm]
      have hz' : ‖z - embed x₀‖₊ < r := by exact_mod_cast (mem_ball_iff_norm.mp hz)
      exact (ENNReal.coe_lt_coe.mpr hz').trans (lt_of_lt_of_le hrR (min_le_right _ _))
    have hshift : AnalyticAt ℂ (fun w : CVec m => w - embed x₀) z :=
      analyticAt_id.sub analyticAt_const
    exact ((q.hasFPowerSeriesOnBall hq).analyticAt_of_mem hzq).comp_of_eq hshift rfl
  · intro x hx
    have hxr : ‖x-x₀‖₊ < r := by exact_mod_cast (mem_ball_iff_norm.mp hx)
    have hxR : x-x₀ ∈ EMetric.ball 0 R := by
      rw [mem_emetric_ball_zero_iff, enorm_eq_nnnorm]
      exact (ENNReal.coe_lt_coe.mpr hxr).trans (lt_of_lt_of_le hrR (min_le_left _ _))
    have hsum := hp.hasSum hxR
    have hxx : x₀ + (x-x₀) = x := by abel
    rw [hxx] at hsum
    change q.sum (embed x - embed x₀) = f x
    rw [← embed_sub]
    unfold FormalMultilinearSeries.sum
    simp only [q, complexSeries, coefficient_apply_embed]
    exact hsum.tsum_eq

end LeanVerification.RealComplexification
