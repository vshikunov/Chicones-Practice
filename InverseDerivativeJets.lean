import LeanVerification.AnalyticMultiplicity
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! The first three actual derivatives of a local analytic inverse. -/

noncomputable section

open Set Filter
open scoped Topology

namespace LeanVerification.InverseDerivativeJets

theorem first {f g : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g (f x))
    (hleft : (fun t => g (f t)) =ᶠ[𝓝 x] id) (hd : deriv f x ≠ 0) :
    deriv g (f x) = 1 / deriv f x := by
  have hc := hg.differentiableAt.hasDerivAt.comp x hf.differentiableAt.hasDerivAt
  have he := (hc.congr_of_eventuallyEq hleft.symm).unique (hasDerivAt_id x)
  exact (eq_div_iff hd).mpr he

theorem eventually_data {f g : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g (f x))
    (hleft : (fun t => g (f t)) =ᶠ[𝓝 x] id) (hd : deriv f x ≠ 0) :
    ∀ᶠ y in 𝓝 x, AnalyticAt ℝ f y ∧ AnalyticAt ℝ g (f y) ∧
      ((fun t => g (f t)) =ᶠ[𝓝 y] id) ∧ deriv f y ≠ 0 := by
  filter_upwards [hf.eventually_analyticAt, hf.continuousAt.eventually hg.eventually_analyticAt,
    eventually_eventually_nhds.mpr hleft,
    hf.deriv.continuousAt.eventually (eventually_ne_nhds hd)] with y hfy hgy hly hdy
  exact ⟨hfy, hgy, hly, hdy⟩

theorem second {f g : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g (f x))
    (hleft : (fun t => g (f t)) =ᶠ[𝓝 x] id) (hd : deriv f x ≠ 0) :
    deriv (deriv g) (f x) = -deriv (deriv f) x / deriv f x ^ 3 := by
  have hevent : (fun t => deriv g (f t)) =ᶠ[𝓝 x] fun t => 1 / deriv f t := by
    filter_upwards [eventually_data hf hg hleft hd] with y hy
    exact first hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
  have hleftd := hg.deriv.differentiableAt.hasDerivAt.comp x hf.differentiableAt.hasDerivAt
  have hrightd := (hasDerivAt_const x (1 : ℝ)).div hf.deriv.differentiableAt.hasDerivAt hd
  have he := (hleftd.congr_of_eventuallyEq hevent.symm).unique hrightd
  have hsolve : deriv (deriv g) (f x) =
      ((0 * deriv f x - 1 * deriv (deriv f) x) / deriv f x ^ 2) / deriv f x :=
    (eq_div_iff hd).mpr he
  rw [hsolve]
  field_simp only [hd]
  ring

theorem third {f g : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g (f x))
    (hleft : (fun t => g (f t)) =ᶠ[𝓝 x] id) (hd : deriv f x ≠ 0) :
    deriv (deriv (deriv g)) (f x) =
      (3 * deriv (deriv f) x ^ 2 - deriv f x * deriv (deriv (deriv f)) x) /
        deriv f x ^ 5 := by
  have hevent : (fun t => deriv (deriv g) (f t)) =ᶠ[𝓝 x]
      fun t => -deriv (deriv f) t / deriv f t ^ 3 := by
    filter_upwards [eventually_data hf hg hleft hd] with y hy
    exact second hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
  have hleftd := hg.deriv.deriv.differentiableAt.hasDerivAt.comp x hf.differentiableAt.hasDerivAt
  have hrightd := hf.deriv.deriv.differentiableAt.hasDerivAt.neg.div
    (hf.deriv.differentiableAt.hasDerivAt.pow 3) (pow_ne_zero 3 hd)
  have he := (hleftd.congr_of_eventuallyEq hevent.symm).unique hrightd
  have hsolve : deriv (deriv (deriv g)) (f x) =
      ((-deriv (deriv (deriv f)) x * deriv f x ^ 3 -
        (-deriv (deriv f) x) * (3 * deriv f x ^ 2 * deriv (deriv f) x)) /
          (deriv f x ^ 3) ^ 2) / deriv f x := by
    apply (eq_div_iff hd).mpr
    simpa using he
  rw [hsolve]
  field_simp only [hd]
  ring

end LeanVerification.InverseDerivativeJets
