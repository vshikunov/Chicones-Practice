import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Algebraic positivity in Lemma 6.1

These theorems verify the finite-dimensional algebra in the inverse-width
comparison. They do not assert the analytic hypotheses of that comparison,
nor the Abel-transfer conclusion for a period function.
-/

namespace LeanVerification.LowerAlgebra

/-- The strict admissibility inequality already places `y` in `(0, 1)`
and makes the manuscript's `chi = 1 - 4 * mu` positive. -/
theorem admissible_bounds (y mu : ℝ) (hmu : 0 < mu)
    (hupper : mu < y - y ^ 2) :
    0 < y ∧ y < 1 ∧ mu < (1 / 4 : ℝ) ∧ 0 < 1 - 4 * mu := by
  have hy : 0 < y := by nlinarith [sq_nonneg y]
  have hy_one : y < 1 := by nlinarith [sq_nonneg (y - 1)]
  have hmu_quarter : mu < (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (y - (1 / 2 : ℝ))]
  exact ⟨hy, hy_one, hmu_quarter, by linarith⟩

/-- The lower polynomial in equation (6.2). -/
noncomputable def lowerPolynomial (y mu : ℝ) : ℝ :=
  y / 4 * (10 * y ^ 2 - 14 * y + 5) + mu * (2 * y ^ 3 - 1 / 2)

/-- Strict positivity of the lower polynomial under the exact strict
admissibility inequality used in Lemma 6.1. -/
theorem lowerPolynomial_pos (y mu : ℝ) (hmu : 0 < mu)
    (hupper : mu < y - y ^ 2) : 0 < lowerPolynomial y mu := by
  obtain ⟨hy, hy_one, _, _⟩ := admissible_bounds y mu hmu hupper
  by_cases hcoef : 0 ≤ 2 * y ^ 3 - (1 / 2 : ℝ)
  · have hquadratic : 0 < 10 * y ^ 2 - 14 * y + 5 := by
      nlinarith [sq_nonneg (10 * y - 7)]
    have hbase : 0 < y / 4 * (10 * y ^ 2 - 14 * y + 5) :=
      mul_pos (div_pos hy (by norm_num)) hquadratic
    have hterm : 0 ≤ mu * (2 * y ^ 3 - (1 / 2 : ℝ)) :=
      mul_nonneg (le_of_lt hmu) hcoef
    unfold lowerPolynomial
    linarith
  · have hcoef_neg : 2 * y ^ 3 - (1 / 2 : ℝ) < 0 := lt_of_not_ge hcoef
    have hstrict : 0 < (y - y ^ 2 - mu) * ((1 / 2 : ℝ) - 2 * y ^ 3) :=
      mul_pos (by linarith) (by linarith)
    have hfactor : 0 ≤ 3 - 2 * y ^ 2 := by nlinarith
    have hnonneg : 0 ≤ y * (2 * y - 1) ^ 2 * (3 - 2 * y ^ 2) / 4 :=
      div_nonneg
        (mul_nonneg (mul_nonneg (le_of_lt hy) (sq_nonneg (2 * y - 1))) hfactor)
        (by norm_num)
    have hidentity : lowerPolynomial y mu =
        y * (2 * y - 1) ^ 2 * (3 - 2 * y ^ 2) / 4 +
          (y - y ^ 2 - mu) * ((1 / 2 : ℝ) - 2 * y ^ 3) := by
      unfold lowerPolynomial
      ring
    rw [hidentity]
    exact add_pos_of_nonneg_of_pos hnonneg hstrict

/-- The normalized value of `(D + 1/2)Q` in Lemma 6.1. -/
noncomputable def normalizedCurvature (y mu delta : ℝ) : ℝ :=
  -mu / 2 + (5 / 4 : ℝ) * y - (7 / 2 : ℝ) * y ^ 2 + delta * y ^ 3

/-- The hypothesized lower bound for `delta` implies a strict positive
normalized curvature. The bound itself is an explicit assumption. -/
theorem normalizedCurvature_pos (y mu delta : ℝ) (hmu : 0 < mu)
    (hupper : mu < y - y ^ 2)
    (hdelta : (5 / 2 : ℝ) + 2 * mu ≤ delta) :
    0 < normalizedCurvature y mu delta := by
  have hy : 0 < y := (admissible_bounds y mu hmu hupper).1
  have hnonneg : 0 ≤ (delta - ((5 / 2 : ℝ) + 2 * mu)) * y ^ 3 :=
    mul_nonneg (by linarith) (le_of_lt (pow_pos hy 3))
  have hidentity : normalizedCurvature y mu delta = lowerPolynomial y mu +
      (delta - ((5 / 2 : ℝ) + 2 * mu)) * y ^ 3 := by
    unfold normalizedCurvature lowerPolynomial
    ring
  rw [hidentity]
  exact add_pos_of_pos_of_nonneg (lowerPolynomial_pos y mu hmu hupper) hnonneg

/-- The inverse-derivative comparison gives the normalized ratio bound.
Here `e1`, `e2`, and `e3` are real numbers representing the first three
inverse-width derivatives. The inverse-function identities identify
`mu = w * e2 / (4 * e1)` and `delta = 3 - e1 * e3 / e2^2`.
This theorem verifies the algebraic implication, not those derivative identities. -/
theorem ratio_bound_from_inverse_derivative_comparison
    (w e1 e2 e3 : ℝ) (he1 : 0 < e1) (he2 : 0 < e2)
    (hcomparison : e1 ^ 2 * e3 ≤ (1 / 2 : ℝ) * e2 ^ 2 * (e1 - w * e2)) :
    (5 / 2 : ℝ) + 2 * (w * e2 / (4 * e1)) ≤ 3 - e1 * e3 / e2 ^ 2 := by
  have he1_ne : e1 ≠ 0 := ne_of_gt he1
  have he2_ne : e2 ≠ 0 := ne_of_gt he2
  have hden : 0 < e1 * e2 ^ 2 := mul_pos he1 (sq_pos_of_pos he2)
  have hidentity :
      (3 - e1 * e3 / e2 ^ 2 - ((5 / 2 : ℝ) + 2 * (w * e2 / (4 * e1)))) *
        (e1 * e2 ^ 2) =
      (1 / 2 : ℝ) * e2 ^ 2 * (e1 - w * e2) - e1 ^ 2 * e3 := by
    field_simp [he1_ne, he2_ne]
    ring
  have hgap : 0 ≤ 3 - e1 * e3 / e2 ^ 2 -
      ((5 / 2 : ℝ) + 2 * (w * e2 / (4 * e1))) := by
    apply nonneg_of_mul_nonneg_left ?_ hden
    rw [hidentity]
    exact sub_nonneg.mpr hcomparison
  linarith

/-- Returning to the original positive algebraic quantities `A`, `B`,
and `C` verifies the finite-dimensional implication in Lemma 6.1.
No differentiability or width-function property is asserted here. -/
theorem unnormalizedCurvature_pos_of_ratio_bound
    (A B C xi F3 : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hQ : 0 < -A + B * xi - C * xi ^ 2)
    (hratio : (5 / 2 : ℝ) + 2 * (A * C / B ^ 2) ≤ B * F3 / C ^ 2) :
    0 < -A / 2 + (5 / 4 : ℝ) * B * xi -
      (7 / 2 : ℝ) * C * xi ^ 2 + F3 * xi ^ 3 := by
  have hB_ne : B ≠ 0 := ne_of_gt hB
  have hC_ne : C ≠ 0 := ne_of_gt hC
  have hB_sq : 0 < B ^ 2 := sq_pos_of_pos hB
  have hscale : 0 < C / B ^ 2 := div_pos hC hB_sq
  have hmu : 0 < A * C / B ^ 2 := div_pos (mul_pos hA hC) hB_sq
  have hidentityQ : C * xi / B - (C * xi / B) ^ 2 - A * C / B ^ 2 =
      (C / B ^ 2) * (-A + B * xi - C * xi ^ 2) := by
    field_simp [hB_ne]
    ring
  have hupper : A * C / B ^ 2 < C * xi / B - (C * xi / B) ^ 2 := by
    apply sub_pos.mp
    rw [hidentityQ]
    exact mul_pos hscale hQ
  have hnormalized := normalizedCurvature_pos
    (C * xi / B) (A * C / B ^ 2) (B * F3 / C ^ 2) hmu hupper hratio
  have hidentity :
      (C / B ^ 2) * (-A / 2 + (5 / 4 : ℝ) * B * xi -
        (7 / 2 : ℝ) * C * xi ^ 2 + F3 * xi ^ 3) =
      normalizedCurvature (C * xi / B) (A * C / B ^ 2) (B * F3 / C ^ 2) := by
    unfold normalizedCurvature
    field_simp [hB_ne, hC_ne]
    ring
  rw [← hidentity] at hnormalized
  exact (mul_pos_iff_of_pos_left hscale).mp hnormalized

end LeanVerification.LowerAlgebra
