import LeanVerification.Loud.RaisedKernel
import LeanVerification.AnalyticDerivativeBounds

/-! The true Euler operators acting on a square-root physical width. -/
noncomputable section
open Filter
open scoped Topology
namespace LeanVerification.EulerWidthCalculus
open Loud
set_option maxHeartbeats 1500000

theorem analyticAt_shift {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) (a : ℝ) :
    AnalyticAt ℝ (energyEulerShift a f) x :=
  (analyticAt_id.mul hf.deriv).add (analyticAt_const.mul hf)

theorem shift_eventuallyEq {f g : ℝ → ℝ} {x : ℝ} (he : f =ᶠ[𝓝 x] g) (a : ℝ) :
    energyEulerShift a f =ᶠ[𝓝 x] energyEulerShift a g := by
  filter_upwards [he,he.deriv] with z hz hdz
  simp only [energyEulerShift,hz,hdz]

theorem shift_rpow_mul {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x)
    (hx : 0 < x) (a p : ℝ) :
    energyEulerShift a (fun v => v^p*f v) x =
      x^p*energyEulerShift (a+p) f x := by
  have hd := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')).mul
    hf.differentiableAt.hasDerivAt
  rw [energyEulerShift,hd.deriv,energyEulerShift,Real.rpow_sub_one hx.ne']
  field_simp
  ring

theorem shift_rpow_mul_eventually {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x)
    (hx : 0 < x) (a p : ℝ) :
    energyEulerShift a (fun v => v^p*f v) =ᶠ[𝓝 x]
      (fun v => v^p*energyEulerShift (a+p) f v) := by
  filter_upwards [hf.eventually_analyticAt,Ioi_mem_nhds hx] with v hv hv0
  exact shift_rpow_mul hv hv0 a p

theorem deriv_sqrt_mul {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) (hx : 0 < x) :
    deriv (fun v => Real.sqrt v*f v) x =
      x^(-(1 : ℝ)/2)*energyEulerShift (1/2) f x := by
  have hd := (Real.hasDerivAt_sqrt hx.ne').mul hf.differentiableAt.hasDerivAt
  rw [hd.deriv,energyEulerShift,Real.sqrt_eq_rpow]
  have he : x^(-(1 : ℝ)/2)=x^((1 : ℝ)/2)/x := by
    convert Real.rpow_sub_one hx.ne' (1/2) using 1 <;> norm_num
  rw [he]
  have hs : (x^((1 : ℝ)/2))^2=x := by
    rw [←Real.sqrt_eq_rpow,Real.sq_sqrt hx.le]
  have hn : x^((1 : ℝ)/2) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  field_simp
  linear_combination -2*f x*hs

theorem raised_sqrt_width_identity {f : ℝ → ℝ} {h : ℝ}
    (hf : AnalyticAt ℝ f h) (hh : 0 < h) :
    energyEulerShift (5/2) (energyEulerShift (3/2)
      (energyEulerShift (1/2) (deriv (fun v => Real.sqrt v*f v)))) h / Real.sqrt h =
      energyEulerShift 2 (energyEulerShift 1 (energyEulerShift 0
        (energyEulerShift (1/2) f))) h / h := by
  let f₀ := energyEulerShift (1/2) f
  let f₁ := energyEulerShift 0 f₀
  let f₂ := energyEulerShift 1 f₁
  have h₀ : AnalyticAt ℝ f₀ h := analyticAt_shift hf _
  have h₁ : AnalyticAt ℝ f₁ h := analyticAt_shift h₀ _
  have h₂ : AnalyticAt ℝ f₂ h := analyticAt_shift h₁ _
  have he₀ : deriv (fun v => Real.sqrt v*f v) =ᶠ[𝓝 h]
      (fun v => v^(-(1 : ℝ)/2)*f₀ v) := by
    filter_upwards [hf.eventually_analyticAt,Ioi_mem_nhds hh] with v hv hv0
    exact deriv_sqrt_mul hv hv0
  have he₁ : energyEulerShift (1/2) (deriv (fun v => Real.sqrt v*f v)) =ᶠ[𝓝 h]
      (fun v => v^(-(1 : ℝ)/2)*f₁ v) := by
    exact (shift_eventuallyEq he₀ (1/2)).trans
      (by simpa only [show (1 : ℝ)/2 + -1/2=0 by ring] using
        shift_rpow_mul_eventually h₀ hh (1/2) (-(1 : ℝ)/2))
  have he₂ : energyEulerShift (3/2)
      (energyEulerShift (1/2) (deriv (fun v => Real.sqrt v*f v))) =ᶠ[𝓝 h]
      (fun v => v^(-(1 : ℝ)/2)*f₂ v) := by
    exact (shift_eventuallyEq he₁ (3/2)).trans
      (by simpa only [show (3 : ℝ)/2 + -1/2=1 by ring] using
        shift_rpow_mul_eventually h₁ hh (3/2) (-(1 : ℝ)/2))
  have he₃ := (shift_eventuallyEq he₂ (5/2)).trans
    (shift_rpow_mul_eventually h₂ hh (5/2) (-(1 : ℝ)/2))
  have hp := he₃.eq_of_nhds
  simp only [show (5 : ℝ)/2 + -1/2=2 by ring] at hp
  rw [hp,Real.sqrt_eq_rpow]
  have hex : h^(-(1 : ℝ)/2)/h^((1 : ℝ)/2)=h⁻¹ := by
    rw [←Real.rpow_sub hh]
    norm_num [Real.rpow_neg_one]
  change h^(-(1 : ℝ)/2)*energyEulerShift 2 f₂ h/h^((1 : ℝ)/2)=energyEulerShift 2 f₂ h/h
  rw [mul_div_right_comm,hex]
  ring

end LeanVerification.EulerWidthCalculus
