import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact algebra for the manuscript's sharpness model

This file checks the explicit real expressions in Section 36.  In particular,
`displayedJacobianValue` is only the displayed expression: this file does not
identify it with the Jacobian of the actual period coefficients.  Similarly,
`aStar` is the displayed positive number, not a formalized third period
coefficient.  The limiting and unfolded quadratics below are explicit
polynomials, not the actual period derivative.

No statement here supplies the analytic inverse/implicit function theorem
application, the analytic extension of the rescaled period derivative, or the
existence of the corresponding periodic orbits.
-/

noncomputable section

namespace LeanVerification.SharpnessAlgebra

def rStar : ℝ := Real.sqrt 105

def dStar : ℝ := (rStar - 11) / 20

def fStar : ℝ := (15 - rStar) / 20

/-- The explicit polynomial formula displayed for the first coefficient. -/
def tauOneFormula (D F : ℝ) : ℝ :=
  (10 * D ^ 2 + (10 * F - 1) * D + 4 * F ^ 2 - 5 * F + 1) / 12

/-- The displayed value; identification with the actual third coefficient
is outside the scope of this file. -/
def aStar : ℝ := (371 - 33 * rStar) / 900000

/-- The displayed value only, without an assertion about an actual Jacobian. -/
def displayedJacobianValue : ℝ := (175 - 19 * rStar) / 6000

theorem rStar_nonneg : 0 ≤ rStar := by
  exact Real.sqrt_nonneg 105

theorem rStar_sq : rStar ^ 2 = 105 := by
  unfold rStar
  exact Real.sq_sqrt (by norm_num)

theorem rStar_bounds : 10 < rStar ∧ rStar < 11 := by
  constructor
  · by_contra h
    have hle : rStar ≤ 10 := le_of_not_gt h
    have hp : 0 ≤ (10 - rStar) * (10 + rStar) :=
      mul_nonneg (sub_nonneg.mpr hle) (by linarith [rStar_nonneg])
    nlinarith [rStar_sq]
  · by_contra h
    have hle : 11 ≤ rStar := le_of_not_gt h
    have hp : 0 ≤ (rStar - 11) * (rStar + 11) :=
      mul_nonneg (sub_nonneg.mpr hle) (by linarith [rStar_nonneg])
    nlinarith [rStar_sq]

/-- The base point lies strictly inside the stated open parameter rectangle. -/
theorem star_in_parameter_region :
    (-1 / 2 : ℝ) < dStar ∧ dStar < 0 ∧ 0 < fStar ∧ fStar < 1 / 2 := by
  rcases rStar_bounds with ⟨hlo, hhi⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [dStar, fStar] <;> linarith

theorem tauOne_parameter_identity (r : ℝ) :
    tauOneFormula ((r - 11) / 20) ((15 - r) / 20) =
      (r ^ 2 - 105) / 1200 := by
  unfold tauOneFormula
  ring

theorem tauOneFormula_at_star : tauOneFormula dStar fStar = 0 := by
  unfold dStar fStar
  rw [tauOne_parameter_identity, rStar_sq]
  norm_num

theorem aStar_pos : 0 < aStar := by
  have hhi := rStar_bounds.2
  unfold aStar
  linarith

theorem aStar_ne_zero : aStar ≠ 0 := ne_of_gt aStar_pos

theorem displayedJacobianValue_neg : displayedJacobianValue < 0 := by
  have hlo := rStar_bounds.1
  unfold displayedJacobianValue
  linarith

theorem displayedJacobianValue_ne_zero : displayedJacobianValue ≠ 0 :=
  ne_of_lt displayedJacobianValue_neg

/-- The explicit quadratic obtained from the prescribed first two coefficients
and the displayed value `aStar`, before any remainder is considered. -/
def unfoldingQuadratic (ε h : ℝ) : ℝ :=
  3 * aStar * (h - ε) * (h - 2 * ε)

theorem unfoldingQuadratic_expansion (ε h : ℝ) :
    unfoldingQuadratic ε h =
      6 * aStar * ε ^ 2 - 9 * aStar * ε * h + 3 * aStar * h ^ 2 := by
  unfold unfoldingQuadratic
  ring

/-- The quadratic has precisely the two indicated roots; no claim about the
zeros of the actual period derivative is made here. -/
theorem unfoldingQuadratic_eq_zero_iff (ε h : ℝ) :
    unfoldingQuadratic ε h = 0 ↔ h = ε ∨ h = 2 * ε := by
  simp [unfoldingQuadratic, mul_eq_zero, aStar_ne_zero, sub_eq_zero]

theorem unfolding_roots_positive_distinct {ε : ℝ} (hε : 0 < ε) :
    0 < ε ∧ 0 < 2 * ε ∧ ε < 2 * ε ∧ ε ≠ 2 * ε := by
  refine ⟨hε, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · intro h
    linarith

theorem hasDerivAt_unfoldingQuadratic (ε h : ℝ) :
    HasDerivAt (unfoldingQuadratic ε) (3 * aStar * (2 * h - 3 * ε)) h := by
  have hleft : HasDerivAt (fun x : ℝ => 3 * aStar * (x - ε)) (3 * aStar) h := by
    simpa only [mul_one] using
      (((hasDerivAt_id h).sub_const ε).const_mul (3 * aStar))
  have hprod := hleft.mul ((hasDerivAt_id h).sub_const (2 * ε))
  dsimp only [id] at hprod
  unfold unfoldingQuadratic
  convert hprod using 1
  ring

theorem deriv_unfoldingQuadratic (ε h : ℝ) :
    deriv (unfoldingQuadratic ε) h = 3 * aStar * (2 * h - 3 * ε) :=
  (hasDerivAt_unfoldingQuadratic ε h).deriv

theorem unfolding_derivative_orientations {ε : ℝ} (hε : 0 < ε) :
    deriv (unfoldingQuadratic ε) ε < 0 ∧
      0 < deriv (unfoldingQuadratic ε) (2 * ε) := by
  rw [deriv_unfoldingQuadratic, deriv_unfoldingQuadratic]
  have hp : 0 < aStar * ε := mul_pos aStar_pos hε
  constructor <;> nlinarith

/-- The normalized limiting polynomial displayed as `Q(0,z)` in the paper. -/
def limitingQuadratic (z : ℝ) : ℝ := unfoldingQuadratic 1 z

theorem unfoldingQuadratic_scaling (ε z : ℝ) :
    unfoldingQuadratic ε (ε * z) = ε ^ 2 * limitingQuadratic z := by
  unfold limitingQuadratic unfoldingQuadratic
  ring

theorem limitingQuadratic_formula (z : ℝ) :
    limitingQuadratic z = 3 * aStar * (z - 1) * (z - 2) := by
  simp only [limitingQuadratic, unfoldingQuadratic, mul_one]

theorem limitingQuadratic_eq_zero_iff (z : ℝ) :
    limitingQuadratic z = 0 ↔ z = 1 ∨ z = 2 := by
  simpa only [limitingQuadratic, mul_one] using
    unfoldingQuadratic_eq_zero_iff 1 z

theorem limiting_derivative_orientations :
    deriv limitingQuadratic 1 < 0 ∧ 0 < deriv limitingQuadratic 2 := by
  simpa only [limitingQuadratic, mul_one] using
    (unfolding_derivative_orientations (ε := 1) (by norm_num))

end LeanVerification.SharpnessAlgebra
