import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pairing the two inverse branches of a quadratic energy coordinate

Both substitutions are ordinary compact change-of-variable integrals.
The left branch orientation is retained explicitly.
-/

noncomputable section

open Set MeasureTheory

namespace LeanVerification

set_option maxHeartbeats 1200000

theorem square_branch_pair_integral (h : ℝ) (f : ℝ → ℝ) (hh : 0 ≤ h)
    (hf : ContinuousOn f (Icc (-Real.sqrt (2 * h)) (Real.sqrt (2 * h)))) :
    IntervalIntegrable (fun E => f (-Real.sqrt (2 * E)) - f (Real.sqrt (2 * E))) volume 0 h ∧
      (∫ E in (0 : ℝ)..h, f (-Real.sqrt (2 * E)) - f (Real.sqrt (2 * E))) =
        -(∫ u in (-Real.sqrt (2 * h))..(Real.sqrt (2 * h)), u * f u) := by
  let r := Real.sqrt (2 * h)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 / 2 = h := by rw [Real.sq_sqrt (by linarith : 0 ≤ 2 * h)]; ring
  have hplus : MapsTo (fun E => Real.sqrt (2 * E)) (Icc 0 h) (Icc (-r) r) := by
    intro E hE
    exact ⟨by linarith [Real.sqrt_nonneg (2 * E)], Real.sqrt_le_sqrt (by linarith [hE.2])⟩
  have hminus : MapsTo (fun E => -Real.sqrt (2 * E)) (Icc 0 h) (Icc (-r) r) := by
    intro E hE
    have hEr := Real.sqrt_le_sqrt (by linarith [hE.2] : 2 * E ≤ 2 * h)
    exact ⟨neg_le_neg hEr, (neg_nonpos.mpr (Real.sqrt_nonneg (2 * E))).trans hr⟩
  have hpc : ContinuousOn (fun E => f (Real.sqrt (2 * E))) (Icc 0 h) :=
    hf.comp (continuous_const.mul continuous_id).sqrt.continuousOn hplus
  have hmc : ContinuousOn (fun E => f (-Real.sqrt (2 * E))) (Icc 0 h) :=
    hf.comp (continuous_const.mul continuous_id).sqrt.neg.continuousOn hminus
  have hpi : IntervalIntegrable (fun E => f (Real.sqrt (2 * E))) volume 0 h := hpc.intervalIntegrable_of_Icc hh
  have hmi : IntervalIntegrable (fun E => f (-Real.sqrt (2 * E))) volume 0 h := hmc.intervalIntegrable_of_Icc hh
  have hde : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 2 / 2) u u := by
    intro u
    convert ((hasDerivAt_id u).pow 2).div_const 2 using 1 <;> simp only [id_eq] <;> ring
  have hEplus : (fun u : ℝ => u ^ 2 / 2) '' uIcc 0 r ⊆ Icc 0 h := by
    rintro E ⟨u, hu, rfl⟩
    rw [uIcc_of_le hr] at hu
    change 0 ≤ u ^ 2 / 2 ∧ u ^ 2 / 2 ≤ h
    exact ⟨by positivity, by nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (add_nonneg hr hu.1)]⟩
  have hEminus : (fun u : ℝ => u ^ 2 / 2) '' uIcc (-r) 0 ⊆ Icc 0 h := by
    rintro E ⟨u, hu, rfl⟩
    rw [uIcc_of_le (neg_nonpos.mpr hr)] at hu
    change 0 ≤ u ^ 2 / 2 ∧ u ^ 2 / 2 ≤ h
    have hp : 0 ≤ (r + u) * (r - u) := mul_nonneg (by linarith [hu.1]) (by linarith [hu.2])
    exact ⟨by positivity, by nlinarith [hp]⟩
  have hsplus := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := r)
    (f := fun u : ℝ => u ^ 2 / 2) (f' := fun u => u)
    (g := fun E => f (Real.sqrt (2 * E))) (fun u _ => hde u) continuousOn_id (hpc.mono hEplus)
  have hsminus := intervalIntegral.integral_comp_mul_deriv' (a := -r) (b := 0)
    (f := fun u : ℝ => u ^ 2 / 2) (f' := fun u => u)
    (g := fun E => f (-Real.sqrt (2 * E))) (fun u _ => hde u) continuousOn_id (hmc.mono hEminus)
  have hiPlus : (∫ u in (0 : ℝ)..r, u * f u) = ∫ E in (0 : ℝ)..h, f (Real.sqrt (2 * E)) := by
    have heq : (∫ u in (0 : ℝ)..r, u * f u) =
        ∫ u in (0 : ℝ)..r, ((fun E => f (Real.sqrt (2 * E))) ∘ (fun v : ℝ => v ^ 2 / 2)) u * u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hr] at hu
      dsimp only [Function.comp_apply]
      rw [show 2 * (u ^ 2 / 2) = u ^ 2 by ring, Real.sqrt_sq hu.1, mul_comm]
    rw [heq, hsplus]
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, hrsq]
  have hiMinus : (∫ u in (-r)..0, u * f u) = -(∫ E in (0 : ℝ)..h, f (-Real.sqrt (2 * E))) := by
    have heq : (∫ u in (-r)..0, u * f u) =
        ∫ u in (-r)..0, ((fun E => f (-Real.sqrt (2 * E))) ∘ (fun v : ℝ => v ^ 2 / 2)) u * u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (neg_nonpos.mpr hr)] at hu
      dsimp only [Function.comp_apply]
      rw [show 2 * (u ^ 2 / 2) = u ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_nonpos hu.2, neg_neg, mul_comm]
    rw [heq, hsminus]
    simp only [neg_sq, hrsq, zero_pow (by norm_num : 2 ≠ 0), zero_div]
    exact intervalIntegral.integral_symm (f := fun E => f (-Real.sqrt (2 * E))) 0 h
  have hfic : ContinuousOn (fun u => u * f u) (Icc (-r) r) := continuousOn_id.mul hf
  have hleft : IntervalIntegrable (fun u => u * f u) volume (-r) 0 :=
    (hfic.mono (Icc_subset_Icc le_rfl hr)).intervalIntegrable_of_Icc (neg_nonpos.mpr hr)
  have hright : IntervalIntegrable (fun u => u * f u) volume 0 r :=
    (hfic.mono (Icc_subset_Icc (neg_nonpos.mpr hr) le_rfl)).intervalIntegrable_of_Icc hr
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  refine ⟨hmi.sub hpi, ?_⟩
  rw [intervalIntegral.integral_sub hmi hpi]
  change (∫ E in (0 : ℝ)..h, f (-Real.sqrt (2 * E))) - (∫ E in (0 : ℝ)..h, f (Real.sqrt (2 * E))) =
    -(∫ u in (-r)..r, u * f u)
  linarith

end LeanVerification
