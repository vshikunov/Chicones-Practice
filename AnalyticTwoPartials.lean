import LeanVerification.Loud.CompactAnalyticIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Analytic partial derivatives in energy and position

The partial derivatives are ordinary one-variable `deriv` operations.
Their analyticity and commutation follow from the actual joint analytic
function; mixed derivative regularity is not a separate hypothesis.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace LeanVerification.AnalyticTwoPartials

set_option maxHeartbeats 800000

def left (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (fun r => f (r, p.2)) p.1

def right (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (fun x => f (p.1, x)) p.2

theorem left_eq_fderiv {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) : left f p = fderiv ℝ f p (1, 0) := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hd.deriv

theorem right_eq_fderiv {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) : right f p = fderiv ℝ f p (0, 1) := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact hd.deriv

theorem analyticAt_left {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : AnalyticAt ℝ f p) : AnalyticAt ℝ (left f) p := by
  let ev : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (1, 0)
  have hd : AnalyticAt ℝ (fun q => fderiv ℝ f q (1, 0)) p :=
    (ev.analyticAt _).comp hf.fderiv
  apply hd.congr
  filter_upwards [hf.eventually_analyticAt] with q hq
  exact (left_eq_fderiv hq.differentiableAt).symm

theorem analyticAt_right {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : AnalyticAt ℝ f p) : AnalyticAt ℝ (right f) p := by
  let ev : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (0, 1)
  have hd : AnalyticAt ℝ (fun q => fderiv ℝ f q (0, 1)) p :=
    (ev.analyticAt _).comp hf.fderiv
  apply hd.congr
  filter_upwards [hf.eventually_analyticAt] with q hq
  exact (right_eq_fderiv hq.differentiableAt).symm

theorem hasFDerivAt_left {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : AnalyticAt ℝ f p) :
    HasFDerivAt (left f)
      ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).comp
        (fderiv ℝ (fderiv ℝ f) p)) p := by
  have hd := (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).hasFDerivAt.comp p
    hf.fderiv.differentiableAt.hasFDerivAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [hf.eventually_analyticAt] with q hq
  exact left_eq_fderiv hq.differentiableAt

theorem hasFDerivAt_right {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : AnalyticAt ℝ f p) :
    HasFDerivAt (right f)
      ((ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).comp
        (fderiv ℝ (fderiv ℝ f) p)) p := by
  have hd := (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).hasFDerivAt.comp p
    hf.fderiv.differentiableAt.hasFDerivAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [hf.eventually_analyticAt] with q hq
  exact right_eq_fderiv hq.differentiableAt

theorem mixed_partials_commute {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : AnalyticAt ℝ f p) : left (right f) p = right (left f) p := by
  rw [left_eq_fderiv (analyticAt_right hf).differentiableAt,
    right_eq_fderiv (analyticAt_left hf).differentiableAt,
    (hasFDerivAt_right hf).fderiv, (hasFDerivAt_left hf).fderiv]
  exact hf.contDiffAt.isSymmSndFDerivAt_of_omega (1, 0) (0, 1)

theorem left_right_right {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : AnalyticAt ℝ f p) : left (right (right f)) p = right (right (left f)) p := by
  rw [mixed_partials_commute (analyticAt_right hf)]
  have he : (fun x => left (right f) (p.1, x)) =ᶠ[𝓝 p.2]
      fun x => right (left f) (p.1, x) := by
    have hh : ∀ᶠ q in 𝓝 p, left (right f) q = right (left f) q := by
      filter_upwards [hf.eventually_analyticAt] with q hq
      exact mixed_partials_commute hq
    exact (continuousAt_const.prodMk continuousAt_id).eventually hh
  exact he.deriv_eq

end LeanVerification.AnalyticTwoPartials
