import LeanVerification.AnalyticTwoPartials
import LeanVerification.CriticalMode

/-!
# Differentiation of an actual analytic mode family

All spatial and energy derivatives below are derivatives of the supplied
joint analytic functions. The differentiated equation and Green derivative
are derived from the undifferentiated equation near the point.
-/

noncomputable section

open Filter
open scoped Topology

namespace LeanVerification.AnalyticModeFamily

open AnalyticTwoPartials

set_option maxHeartbeats 1000000

theorem hasDerivAt_left_slice {f : ℝ × ℝ → ℝ} {q : ℝ × ℝ}
    (hf : AnalyticAt ℝ f q) : HasDerivAt (fun L => f (L, q.2)) (left f q) q.1 :=
  (hf.comp_of_eq (f := fun L : ℝ => (L, q.2))
    (analyticAt_id.prod analyticAt_const) rfl).differentiableAt.hasDerivAt

theorem hasDerivAt_right_slice {f : ℝ × ℝ → ℝ} {q : ℝ × ℝ}
    (hf : AnalyticAt ℝ f q) : HasDerivAt (fun x => f (q.1, x)) (right f q) q.2 :=
  (hf.comp_of_eq (f := fun x : ℝ => (q.1, x))
    (analyticAt_const.prod analyticAt_id) rfl).differentiableAt.hasDerivAt

theorem energy_variation_equation {Y : ℝ × ℝ → ℝ} {W : ℝ → ℝ} {q : ℝ × ℝ}
    (hY : AnalyticAt ℝ Y q)
    (heq : ∀ᶠ z : ℝ × ℝ in 𝓝 q,
      2 * (z.1 - W z.2) * right Y z + deriv W z.2 * Y z = 1) :
    2 * (q.1 - W q.2) * right (left Y) q + deriv W q.2 * left Y q =
      -2 * right Y q := by
  have hd := (((hasDerivAt_id q.1).sub_const (W q.2)).const_mul 2).mul
    (hasDerivAt_left_slice (analyticAt_right hY)) |>.add
      ((hasDerivAt_left_slice hY).const_mul (deriv W q.2))
  have hh : (fun L => 2 * (L - W q.2) * right Y (L, q.2) + deriv W q.2 * Y (L, q.2))
      =ᶠ[𝓝 q.1] fun _ => (1 : ℝ) :=
    (continuousAt_id.prodMk continuousAt_const).eventually heq
  have hz := (hd.congr_of_eventuallyEq hh.symm).unique (hasDerivAt_const q.1 (1 : ℝ))
  rw [mixed_partials_commute hY] at hz
  dsimp only [id_eq] at hz
  nlinarith only [hz]

def modeResidual (p Q U : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  p q * right (right U) q + right p q * right U q + p q * Q q * U q

theorem differentiated_mode_equation {p Q U : ℝ × ℝ → ℝ} {q : ℝ × ℝ}
    (hp : AnalyticAt ℝ p q) (hQ : AnalyticAt ℝ Q q) (hU : AnalyticAt ℝ U q)
    (heq : ∀ᶠ z in 𝓝 q, modeResidual p Q U z = 0) :
    p q * right (right (left U)) q + right p q * right (left U) q + p q * Q q * left U q =
      -left p q * right (right U) q - right (left p) q * right U q -
        (left p q * Q q + p q * left Q q) * U q := by
  have hd := ((hasDerivAt_left_slice hp).mul
    (hasDerivAt_left_slice (analyticAt_right (analyticAt_right hU)))).add
      ((hasDerivAt_left_slice (analyticAt_right hp)).mul
        (hasDerivAt_left_slice (analyticAt_right hU))) |>.add
          (((hasDerivAt_left_slice hp).mul (hasDerivAt_left_slice hQ)).mul
            (hasDerivAt_left_slice hU))
  have he : (fun L => modeResidual p Q U (L, q.2)) =ᶠ[𝓝 q.1] fun _ => (0 : ℝ) :=
    (continuousAt_id.prodMk continuousAt_const).eventually heq
  have hz := (hd.congr_of_eventuallyEq he.symm).unique (hasDerivAt_const q.1 (0 : ℝ))
  rw [left_right_right hU, mixed_partials_commute hp, mixed_partials_commute hU] at hz
  nlinarith only [hz]

theorem hasDerivAt_actual_greenBoundary {p Q U : ℝ × ℝ → ℝ} {q : ℝ × ℝ}
    (hp : AnalyticAt ℝ p q) (hQ : AnalyticAt ℝ Q q) (hU : AnalyticAt ℝ U q)
    (heq : ∀ᶠ z in 𝓝 q, modeResidual p Q U z = 0) :
    HasDerivAt
      (CriticalMode.greenBoundary (fun x => p (q.1, x)) (fun x => left p (q.1, x))
        (fun x => U (q.1, x)) (fun x => right U (q.1, x))
        (fun x => left U (q.1, x)) (fun x => right (left U) (q.1, x)))
      (CriticalMode.greenDensity (fun x => p (q.1, x)) (fun x => left p (q.1, x))
        (fun x => Q (q.1, x)) (fun x => left Q (q.1, x))
        (fun x => U (q.1, x)) (fun x => right U (q.1, x)) q.2) q.2 := by
  exact CriticalMode.hasDerivAt_greenBoundary (hasDerivAt_right_slice hp)
    (hasDerivAt_right_slice (analyticAt_left hp)) (hasDerivAt_right_slice hU)
    (hasDerivAt_right_slice (analyticAt_right hU))
    (hasDerivAt_right_slice (analyticAt_left hU))
    (hasDerivAt_right_slice (analyticAt_right (analyticAt_left hU)))
    heq.self_of_nhds (differentiated_mode_equation hp hQ hU heq)

end LeanVerification.AnalyticModeFamily
