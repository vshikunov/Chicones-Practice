import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Exact regional algebra for the outer natural-gauge comparison in the
canonical period argument.  The Bernstein identity is an explicit polynomial
certificate for the complete scalar numerator, not a sign assumption. -/

namespace LeanVerification.CanonicalOuter

noncomputable section

def numerator (r : ℝ) : ℝ :=
  -1305000000*r^10 - 247950000*r^9 - 1428870000*r^8 - 105020600*r^7 +
  1984572793*r^6 + 114148200*r^5 + 3133359586*r^4 - 157171800*r^3 +
  944186793*r^2 - 128390600*r + 13130000

theorem numerator_bernstein (r : ℝ) :
    numerator r - 1000000*(800*r^2 - 130*r + 13) =
      (1269531250000/59049 : ℝ)*(3/5-r)^10 +
      (22125390625000/59049 : ℝ)*r*(3/5-r)^9 +
      (24033566796875/2187 : ℝ)*r^2*(3/5-r)^8 +
      (1405181950000000/19683 : ℝ)*r^3*(3/5-r)^7 +
      (5632344642531250/19683 : ℝ)*r^4*(3/5-r)^6 +
      (1733825839187500/2187 : ℝ)*r^5*(3/5-r)^5 +
      (28719020505124375/19683 : ℝ)*r^6*(3/5-r)^4 +
      (33831899070197500/19683 : ℝ)*r^7*(3/5-r)^3 +
      (2706825604160000/2187 : ℝ)*r^8*(3/5-r)^2 +
      (29097046605355000/59049 : ℝ)*r^9*(3/5-r) +
      (4778091179582500/59049 : ℝ)*r^10 := by
  unfold numerator
  ring

theorem numerator_quadratic_lower (r : ℝ) (hr : 0 ≤ r) (hupper : r ≤ 3/5) :
    1000000*(800*r^2 - 130*r + 13) ≤ numerator r := by
  have hsub : 0 ≤ 3/5-r := sub_nonneg.mpr hupper
  have h : 0 ≤ numerator r - 1000000*(800*r^2 - 130*r + 13) := by
    rw [numerator_bernstein]
    positivity
  linarith

theorem quadratic_positive (r : ℝ) : 0 < 800*r^2 - 130*r + 13 := by
  nlinarith [sq_nonneg (r - 13/160)]

theorem numerator_positive (r : ℝ) (hr : 0 ≤ r) (hupper : r ≤ 3/5) :
    0 < numerator r := by
  have hl := numerator_quadratic_lower r hr hupper
  have hq := quadratic_positive r
  linarith

def kernelD (r : ℝ) : ℝ := 1 + (19/100)*r + r^2

def differentialA (r : ℝ) : ℝ := (3-r^2)/(1+r^2)

def residueLower (r : ℝ) : ℝ :=
  let D := kernelD r
  let U := 1 + (19/200)*r
  let a := differentialA r
  let B := 4*U+a*D
  let C := 2+2*a*U
  C - 5*B^2/(28*D)

def tailLower (r : ℝ) : ℝ :=
  27/(5*(1+r^2))*(13/100-(6/25)*r^2+r^4/4-(29/120)*r^6)

def scalarComparison (r : ℝ) : ℝ :=
  tailLower r + (91/100)*residueLower r - (637/100000)*kernelD r

theorem comparison_cleared_numerator (r : ℝ) (hr : 0 ≤ r) :
    10000000*(1+r^2)^2*(100*r^2+19*r+100)*scalarComparison r = numerator r := by
  have h1 : 1+r^2 ≠ 0 := ne_of_gt (by positivity)
  have hD : 1+(19/100)*r+r^2 ≠ 0 := ne_of_gt (by positivity)
  unfold scalarComparison tailLower residueLower kernelD differentialA numerator
  dsimp only
  field_simp
  <;> ring

theorem scalarComparison_positive (r : ℝ) (hr : 0 ≤ r) (hupper : r ≤ 3/5) :
    0 < scalarComparison r := by
  have hn := numerator_positive r hr hupper
  have he := comparison_cleared_numerator r hr
  have hf : 0 < 10000000*(1+r^2)^2*(100*r^2+19*r+100) := by positivity
  by_contra h
  have hp := mul_nonpos_of_nonneg_of_nonpos hf.le (le_of_not_gt h)
  linarith

end
end LeanVerification.CanonicalOuter
