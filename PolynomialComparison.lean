import LeanVerification.LowerAlgebra
import Mathlib.Tactic.Positivity

/-! A coefficient comparison for the quartic curvature numerator and its
sextic directional derivative. All coefficient signs must be discharged by
the concrete regional certificates. -/
noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 1000000

def quarticValue (p0 p1 p2 p3 p4 x : ℝ) : ℝ :=
  p0+p1*x+p2*x^2+p3*x^3+p4*x^4

def sexticValue (r0 r1 r2 r3 r4 r5 r6 x : ℝ) : ℝ :=
  r0+r1*x+r2*x^2+r3*x^3+r4*x^4+r5*x^5+r6*x^6

theorem quartic_sextic_identity (p0 p1 p2 p3 p4 r0 r1 r2 r3 r4 r5 r6 x : ℝ) :
    -p4*sexticValue r0 r1 r2 r3 r4 r5 r6 x=
      -p4*r0+(-p4*r1)*x+(-p4*r2+r6*p0)*x^2+
      (-p4*r3+r6*p1)*x^3+(-p4*r4+r6*p2)*x^4+
      (-p4*r5+r6*p3)*x^5-r6*x^2*quarticValue p0 p1 p2 p3 p4 x := by
  dsimp only [quarticValue,sexticValue]
  ring

theorem sextic_pos_of_quartic_pos {p0 p1 p2 p3 p4 r0 r1 r2 r3 r4 r5 r6 x : ℝ}
    (hx : 0<x) (hp4 : p4<0) (hr0 : 0≤r0) (hr1 : 0<r1)
    (hr2 : 0≤r2) (hr3 : 0≤r3) (hr4 : 0≤r4) (hr5 : 0≤r5)
    (hs0 : 0≤ -p4*r2+r6*p0) (hs1 : 0≤ -p4*r3+r6*p1)
    (hs2 : 0≤ -p4*r4+r6*p2) (hs3 : 0≤ -p4*r5+r6*p3)
    (hp : 0<quarticValue p0 p1 p2 p3 p4 x) :
    0<sexticValue r0 r1 r2 r3 r4 r5 r6 x := by
  by_cases hr6 : 0≤r6
  · unfold sexticValue
    have hfirst : 0<r0+r1*x := add_pos_of_nonneg_of_pos hr0 (mul_pos hr1 hx)
    positivity
  · have hr6n : r6<0 := lt_of_not_ge hr6
    have hsum : 0< -p4*r0+(-p4*r1)*x+(-p4*r2+r6*p0)*x^2+
        (-p4*r3+r6*p1)*x^3+(-p4*r4+r6*p2)*x^4+
        (-p4*r5+r6*p3)*x^5-r6*x^2*quarticValue p0 p1 p2 p3 p4 x := by
      have hfirst : 0< -p4*r0+(-p4*r1)*x :=
        add_pos_of_nonneg_of_pos (mul_nonneg (neg_pos.mpr hp4).le hr0)
          (mul_pos (mul_pos (neg_pos.mpr hp4) hr1) hx)
      have hlast : 0< -(r6*x^2*quarticValue p0 p1 p2 p3 p4 x) :=
        neg_pos.mpr (mul_neg_of_neg_of_pos
          (mul_neg_of_neg_of_pos hr6n (sq_pos_of_pos hx)) hp)
      linarith [mul_nonneg hs0 (sq_nonneg x),mul_nonneg hs1 (pow_pos hx 3).le,
        mul_nonneg hs2 (pow_pos hx 4).le,mul_nonneg hs3 (pow_pos hx 5).le]
    rw [←quartic_sextic_identity] at hsum
    exact pos_of_mul_pos_right hsum (neg_pos.mpr hp4).le

end LeanVerification.PositiveDCompletion
