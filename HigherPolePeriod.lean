import LeanVerification.SpectralWidth
import LeanVerification.WeightedCompactDerivatives

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.HigherPole

set_option maxHeartbeats 1500000

/-- Index `n` represents a pole of order `n+1`. These kernels are
explicit principal parts, not ordinary signed spectral atoms. -/
def angularKernel (n : ℕ) (h t θ : ℝ) : ℝ :=
  (t - h * Real.sin θ ^ 2)⁻¹ ^ (n + 1) +
    2 * (n + 1 : ℝ) * (h * Real.sin θ ^ 2) * (t - h * Real.sin θ ^ 2)⁻¹ ^ (n + 2)

def period (n : ℕ) (h t : ℝ) : ℝ :=
  Real.sqrt 2 * ∫ θ in Ioc (0 : ℝ) (Real.pi / 2), angularKernel n h t θ

def width (n : ℕ) (A t v : ℝ) : ℝ :=
  A * Real.sqrt v / (t - v) ^ (n + 1)

theorem analyticAt_angularKernel {h t θ : ℝ} (hh : 0 < h) (ht : h < t) (n : ℕ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ => angularKernel n h p.1 p.2) (t, θ) := by
  have hsin : AnalyticAt ℝ Real.sin θ := by
    have hc : AnalyticAt ℂ Complex.sin (θ : ℂ) := Complex.differentiable_sin.analyticAt _
    simpa only [← Complex.ofReal_sin, Complex.ofReal_re] using hc.re_ofReal
  have hv : AnalyticAt ℝ (fun p : ℝ × ℝ => h * Real.sin p.2 ^ 2) (t, θ) :=
    analyticAt_const.mul (((hsin.comp_of_eq analyticAt_snd rfl)).pow 2)
  have hn : t - h * Real.sin θ ^ 2 ≠ 0 :=
    (sub_pos.mpr ((AbelCauchy.angular_energy_mem hh θ).2.trans_lt ht)).ne'
  have hd := (analyticAt_fst.sub hv).inv hn
  exact (hd.pow (n + 1)).add ((analyticAt_const.mul hv).mul (hd.pow (n + 2)))

theorem hasDerivAt_angularKernel {h t θ : ℝ} (hh : 0 < h) (ht : h < t) (n : ℕ) :
    HasDerivAt (fun s => angularKernel n h s θ)
      (-(n + 1 : ℝ) * angularKernel (n + 1) h t θ) t := by
  have hn : t - h * Real.sin θ ^ 2 ≠ 0 :=
    (sub_pos.mpr ((AbelCauchy.angular_energy_mem hh θ).2.trans_lt ht)).ne'
  have hd := ((hasDerivAt_id t).sub_const (h * Real.sin θ ^ 2)).inv hn
  have hd' : HasDerivAt (fun s : ℝ => (s - h * Real.sin θ ^ 2)⁻¹)
      (-((t - h * Real.sin θ ^ 2)⁻¹ ^ 2)) t := by
    convert hd using 1 <;> simp [div_eq_mul_inv, inv_pow]
  have he := (hd'.pow (n + 1)).add
    ((hd'.pow (n + 2)).const_mul (2 * (n + 1 : ℝ) * (h * Real.sin θ ^ 2)))
  apply he.congr_deriv
  simp only [angularKernel, id_eq, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
    show n + 2 - 1 = n + 1 by omega, Nat.cast_ofNat, one_mul, pow_succ]
  ring

theorem hasDerivAt_period {h t : ℝ} (hh : 0 < h) (ht : h < t) (n : ℕ) :
    HasDerivAt (period n h) (-(n + 1 : ℝ) * period (n + 1) h t) t := by
  have hω : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) (Real.pi / 2)) :=
    (continuous_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hi := WeightedCompactIntegral.weightedIntegral_all_derivatives_on_compact
    isCompact_Icc (fun θ (_ : θ ∈ Icc (0 : ℝ) (Real.pi / 2)) =>
      analyticAt_angularKernel hh ht n) measurableSet_Ioc Ioc_subset_Icc_self hω
  have he := (hi.2.2 1 (fun _ => (1 : ℝ))).2
  simp only [one_mul] at hi he
  change iteratedDeriv 1 (fun s => ∫ θ in Ioc (0 : ℝ) (Real.pi / 2),
    angularKernel n h s θ) t =
      ∫ θ in Ioc (0 : ℝ) (Real.pi / 2), iteratedDeriv 1 (fun s => angularKernel n h s θ) t at he
  simp only [iteratedDeriv_one] at he
  have hd := hi.1.differentiableAt.hasDerivAt.const_mul (Real.sqrt 2)
  apply hd.congr_deriv
  rw [he]
  simp only [(hasDerivAt_angularKernel hh ht n).deriv, integral_const_mul, period]
  ring

theorem iteratedDeriv_period_zero {h t : ℝ} (hh : 0 < h) (ht : h < t) (n : ℕ) :
    iteratedDeriv n (period 0 h) t = (-1 : ℝ) ^ n * (n.factorial : ℝ) * period n h t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have he : iteratedDeriv n (period 0 h) =ᶠ[𝓝 t]
        (fun s => (-1 : ℝ) ^ n * (n.factorial : ℝ) * period n h s) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact ih hs
    rw [iteratedDeriv_succ, he.deriv_eq,
      ((hasDerivAt_period hh ht n).const_mul ((-1 : ℝ) ^ n * (n.factorial : ℝ))).deriv,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

theorem period_zero_eq {h t : ℝ} (hh : 0 < h) (ht : h < t) :
    period 0 h t = Real.pi * Real.sqrt t / (Real.sqrt 2 * (t - h) ^ ((3 : ℝ) / 2)) := by
  have he : (fun θ => angularKernel 0 h t θ) = AbelCauchy.angularKernel h t := by
    funext θ
    have hn : t - h * Real.sin θ ^ 2 ≠ 0 :=
      (sub_pos.mpr ((AbelCauchy.angular_energy_mem hh θ).2.trans_lt ht)).ne'
    simp only [angularKernel, AbelCauchy.angularKernel, Nat.cast_zero, zero_add, pow_one]
    field_simp
    <;> ring
  rw [period, he, ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
    AbelCauchy.integral_angularKernel hh ht]
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hr : (t - h) ^ ((3 : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (sub_pos.mpr ht) _).ne'
  field_simp
  linear_combination (Real.pi * Real.sqrt t * (t - h) ^ ((3 : ℝ) / 2)) *
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

theorem hasDerivAt_width {n : ℕ} {A t v : ℝ} (hv : 0 < v) (ht : v < t) :
    HasDerivAt (width n A t)
      (A * ((1 / (2 * Real.sqrt v)) * (t - v)⁻¹ ^ (n + 1) +
        Real.sqrt v * ((n + 1 : ℝ) * (t - v)⁻¹ ^ (n + 2)))) v := by
  have hd := ((hasDerivAt_const v t).sub (hasDerivAt_id v)).inv (sub_pos.mpr ht).ne'
  have hd' : HasDerivAt (fun u : ℝ => (t - u)⁻¹) ((t - v)⁻¹ ^ 2) v := by
    convert hd using 1 <;> simp
  have he := ((Real.hasDerivAt_sqrt hv.ne').mul (hd'.pow (n + 1))).const_mul A
  convert he using 1
  · funext u
    simp only [width, div_eq_mul_inv, inv_pow]
    ring
  · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
    ring

theorem angularPeriod_width {h t A : ℝ} (hh : 0 < h) (ht : h < t) (n : ℕ) :
    SpectralWidth.angularPeriod (width n A t) h = A * period n h t := by
  unfold SpectralWidth.angularPeriod period
  rw [← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro θ hθ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])
  have hv : 0 < h * Real.sin θ ^ 2 := mul_pos hh (sq_pos_of_pos hs)
  have hvt : h * Real.sin θ ^ 2 < t := (AbelCauchy.angular_energy_mem hh θ).2.trans_lt ht
  have hsq : Real.sqrt (h * Real.sin θ ^ 2) = Real.sqrt h * Real.sin θ := by
    rw [Real.sqrt_mul hh.le, Real.sqrt_sq hs.le]
  have hp : Real.sqrt (2 * h) * Real.sin θ = Real.sqrt 2 * Real.sqrt (h * Real.sin θ ^ 2) := by
    rw [hsq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  dsimp only
  rw [(hasDerivAt_width hv hvt).deriv]
  change 2 * Real.sqrt (2 * h) * Real.sin θ * _ = _
  rw [show 2 * Real.sqrt (2 * h) * Real.sin θ =
    2 * Real.sqrt 2 * Real.sqrt (h * Real.sin θ ^ 2) by rw [mul_assoc, hp]; ring]
  unfold angularKernel
  have hsn : Real.sqrt (h * Real.sin θ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have hc : 2 * Real.sqrt (h * Real.sin θ ^ 2) *
      (1 / (2 * Real.sqrt (h * Real.sin θ ^ 2))) = 1 :=
    mul_one_div_cancel (mul_ne_zero (by norm_num) hsn)
  linear_combination
    (2 * A * Real.sqrt 2 * (n + 1 : ℝ) * (t - h * Real.sin θ ^ 2)⁻¹ ^ (n + 2)) *
      Real.sq_sqrt hv.le +
    (A * Real.sqrt 2 * (t - h * Real.sin θ ^ 2)⁻¹ ^ (n + 1)) * hc

/-- The displayed higher-pole period formula, with every parameter
differentiation justified by actual joint analyticity on the compact
angular interval. Pole order is `n+1`, so the factorial is `n!`. -/
theorem higher_pole_period {h t A : ℝ} (hh : 0 < h) (ht : h < t) (n : ℕ) :
    SpectralWidth.angularPeriod (width n A t) h =
      A / (n.factorial : ℝ) * (-1 : ℝ) ^ n *
        iteratedDeriv n (fun s : ℝ =>
          Real.pi * Real.sqrt s / (Real.sqrt 2 * (s - h) ^ ((3 : ℝ) / 2))) t := by
  have he : period 0 h =ᶠ[𝓝 t] (fun s : ℝ =>
      Real.pi * Real.sqrt s / (Real.sqrt 2 * (s - h) ^ ((3 : ℝ) / 2))) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact period_zero_eq hh hs
  rw [← he.iteratedDeriv_eq n, iteratedDeriv_period_zero hh ht, angularPeriod_width hh ht]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hp : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  field_simp [hn]
  linear_combination -A * (n.factorial : ℝ) * period n h t * hp

end LeanVerification.HigherPole
