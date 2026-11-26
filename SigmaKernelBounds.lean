import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Integrable quadratic majorants for the fixed-line sigma kernel. -/

noncomputable section
open MeasureTheory

namespace LeanVerification.SigmaKernel
set_option maxHeartbeats 500000

def tailConstant (a M : ℝ) : ℝ := a/(a+M+1)

theorem tailConstant_pos {a M : ℝ} (ha : 0<a) (hM : 0≤M) :
    0<tailConstant a M := div_pos ha (by linarith)

theorem quadratic_lower_bound {a M s b : ℝ} (ha : 0<a) (hM : 0≤M)
    (hk : a≤s^2+b) (hb : |b|≤M) :
    tailConstant a M*(1+s^2)≤s^2+b := by
  rw [tailConstant,div_mul_eq_mul_div]
  apply (div_le_iff₀ (by linarith : 0<a+M+1)).mpr
  have hb' : 0≤b+M := by linarith [(abs_le.mp hb).1]
  have hk' : 0≤s^2+b-a := sub_nonneg.mpr hk
  nlinarith [mul_nonneg ha.le hb',mul_nonneg (by linarith : 0≤M+1) hk']

theorem reciprocal_bound {a M s b : ℝ} (ha : 0<a) (hM : 0≤M)
    (hk : a≤s^2+b) (hb : |b|≤M) :
    1/(s^2+b)≤(tailConstant a M)⁻¹/(1+s^2) := by
  have hc := tailConstant_pos ha hM
  have hp : 0<1+s^2 := by positivity
  calc
    1/(s^2+b) ≤ 1/(tailConstant a M*(1+s^2)) :=
      one_div_le_one_div_of_le (mul_pos hc hp) (quadratic_lower_bound ha hM hk hb)
    _ = _ := by rw [one_div,mul_inv]; rfl

theorem reciprocal_sq_bound {a M s b : ℝ} (ha : 0<a) (hM : 0≤M)
    (hk : a≤s^2+b) (hb : |b|≤M) :
    1/(s^2+b)^2≤((tailConstant a M)⁻¹)^2/(1+s^2)^2 := by
  have hkpos : 0<s^2+b := ha.trans_le hk
  have hcpos := tailConstant_pos ha hM
  have he := sq_le_sq₀ (by positivity : 0≤1/(s^2+b))
    (by positivity : 0≤(tailConstant a M)⁻¹/(1+s^2))
  have h := he.mpr (reciprocal_bound ha hM hk hb)
  simpa only [div_pow,one_pow] using h

theorem integrable_quadratic_tail (C : ℝ) :
    Integrable (fun s : ℝ => C/(1+s^2)) := by
  simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C

theorem integrable_quartic_tail (C : ℝ) :
    Integrable (fun s : ℝ => C/(1+s^2)^2) := by
  have hi : Integrable (fun s : ℝ => 1/(1+s^2)^2) := by
    apply integrable_inv_one_add_sq.mono'
      ((continuous_const.div (by fun_prop) (fun s : ℝ => by positivity) :
        Continuous (fun s : ℝ => 1/(1+s^2)^2)).aestronglyMeasurable)
    filter_upwards [] with s
    change ‖(1 : ℝ)/(1+s^2)^2‖≤(1+s^2)⁻¹
    rw [Real.norm_of_nonneg (by positivity : 0≤1/(1+s^2)^2)]
    have hp : 0<1+s^2 := by positivity
    calc
      1/(1+s^2)^2 ≤ 1/(1+s^2) := one_div_le_one_div_of_le hp (by nlinarith [sq_nonneg s])
      _ = _ := one_div _
  convert hi.const_mul C using 1
  funext s
  ring

/-- The original lower gap and bounded perturbation give one common
integrable majorant for both the kernel and its energy derivative. -/
theorem exists_integrable_sigma_majorants {a M N : ℝ}
    (ha : 0<a) (hM : 0≤M) (hN : 0≤N) :
    ∃ C>0, Integrable (fun s : ℝ => C/(1+s^2)) ∧
      Integrable (fun s : ℝ => (N*C^2)/(1+s^2)^2) ∧
      ∀ s b n : ℝ, a≤s^2+b → |b|≤M → |n|≤N →
        |1/(s^2+b)|≤C/(1+s^2) ∧ |n/(s^2+b)^2|≤(N*C^2)/(1+s^2)^2 := by
  let C := (tailConstant a M)⁻¹
  have hC : 0<C := inv_pos.mpr (tailConstant_pos ha hM)
  refine ⟨C,hC,integrable_quadratic_tail C,integrable_quartic_tail (N*C^2),?_⟩
  intro s b n hk hb hn
  have hkpos : 0<s^2+b := ha.trans_le hk
  constructor
  · rw [abs_of_pos (one_div_pos.mpr hkpos)]
    exact reciprocal_bound ha hM hk hb
  · rw [abs_div,abs_of_nonneg (sq_nonneg (s^2+b))]
    calc
      |n|/(s^2+b)^2 ≤ N/(s^2+b)^2 :=
        div_le_div_of_nonneg_right hn (sq_nonneg _)
      _ = N*(1/(s^2+b)^2) := by ring
      _ ≤ N*(C^2/(1+s^2)^2) := mul_le_mul_of_nonneg_left (reciprocal_sq_bound ha hM hk hb) hN
      _ = _ := by ring

end LeanVerification.SigmaKernel
