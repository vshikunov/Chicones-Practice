import LeanVerification.AnalyticDerivativeBounds
import Mathlib.Analysis.Complex.RealDeriv

/-! Every ordinary real derivative of the real restriction of a holomorphic
germ is the real part of its corresponding complex derivative. -/
noncomputable section
open Filter
open scoped Topology
namespace LeanVerification.RealSliceDerivatives

theorem hasDerivAt_real_part {F : ℂ → ℂ} {h : ℝ}
    (hF : AnalyticAt ℂ F (h : ℂ)) :
    HasDerivAt (fun x : ℝ => (F (x : ℂ)).re) (deriv F (h : ℂ)).re h :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt h hF.differentiableAt.hasDerivAt.comp_ofReal

theorem iteratedDeriv_real_part {F : ℂ → ℂ} {h : ℝ}
    (hF : AnalyticAt ℂ F (h : ℂ)) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => (F (x : ℂ)).re) h =
      (iteratedDeriv n F (h : ℂ)).re := by
  induction n generalizing h with
  | zero => simp
  | succ n ih =>
    have he : (fun x : ℝ => iteratedDeriv n (fun y : ℝ => (F (y : ℂ)).re) x) =ᶠ[𝓝 h]
        (fun x : ℝ => (iteratedDeriv n F (x : ℂ)).re) := by
      filter_upwards [Complex.continuous_ofReal.continuousAt.eventually hF.eventually_analyticAt] with x hx
      exact ih hx
    have ha : AnalyticAt ℂ (iteratedDeriv n F) (h : ℂ) := by
      simpa only [iteratedDeriv_eq_iterate] using hF.iterated_deriv n
    simp only [iteratedDeriv_succ]
    rw [he.deriv_eq]
    exact (hasDerivAt_real_part ha).deriv

end LeanVerification.RealSliceDerivatives
