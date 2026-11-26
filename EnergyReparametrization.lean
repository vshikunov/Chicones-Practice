import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

/-!
# Energy changes at a stationary period

These are the first- and second-derivative identities underlying Lemma 2.2
of `chicone_conjecture_updated_v7.tex`. The hypotheses below are explicit
regularity hypotheses on arbitrary real functions; no assertion that the
Loud period integral has these properties is assumed as a new axiom.

The second-derivative identity is stated for globally differentiable
functions. This file does not formalize analytic continuation of the
period integral, zero multiplicities, or the main theorem of the paper.
-/

namespace LeanVerification.EnergyReparametrization

/-- A regular change of energy preserves stationarity at a specified point. -/
theorem regular_change_preserves_stationarity
    {T χ : ℝ → ℝ} {s t' k : ℝ}
    (hT : HasDerivAt T t' (χ s)) (hχ : HasDerivAt χ k s)
    (hk : k ≠ 0) :
    deriv (T ∘ χ) s = 0 ↔ t' = 0 := by
  rw [(hT.comp s hχ).deriv]
  simp [mul_eq_zero, hk]

/-- At a stationary point the second chain-rule term vanishes. -/
theorem stationary_curvature_formula
    {T χ : ℝ → ℝ} {s t'' k'' : ℝ}
    (hT : Differentiable ℝ T) (hχ : Differentiable ℝ χ)
    (hT2 : HasDerivAt (deriv T) t'' (χ s))
    (hχ2 : HasDerivAt (deriv χ) k'' s)
    (hcritical : deriv T (χ s) = 0) :
    deriv (deriv (T ∘ χ)) s = (deriv χ s) ^ 2 * t'' := by
  have hchain : deriv (T ∘ χ) =
      (fun x => deriv T (χ x) * deriv χ x) := by
    funext x
    exact deriv_comp x (hT (χ x)) (hχ x)
  have hcalc : HasDerivAt (fun x => deriv T (χ x) * deriv χ x)
      (t'' * deriv χ s * deriv χ s + deriv T (χ s) * k'') s :=
    (hT2.comp s (hχ s).hasDerivAt).mul hχ2
  rw [hchain, hcalc.deriv, hcritical]
  ring

/-- A nonzero energy derivative preserves positive critical curvature. -/
theorem regular_change_preserves_positive_curvature
    {T χ : ℝ → ℝ} {s t'' k'' : ℝ}
    (hT : Differentiable ℝ T) (hχ : Differentiable ℝ χ)
    (hT2 : HasDerivAt (deriv T) t'' (χ s))
    (hχ2 : HasDerivAt (deriv χ) k'' s)
    (hcritical : deriv T (χ s) = 0)
    (hk : deriv χ s ≠ 0) (hpositive : 0 < t'') :
    0 < deriv (deriv (T ∘ χ)) s := by
  rw [stationary_curvature_formula hT hχ hT2 hχ2 hcritical]
  exact mul_pos (sq_pos_of_ne_zero hk) hpositive

end LeanVerification.EnergyReparametrization
