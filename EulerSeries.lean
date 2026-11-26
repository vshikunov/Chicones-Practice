import LeanVerification.ScalarSeries
import LeanVerification.Loud.RaisedKernel

noncomputable section

open Set Filter
open scoped Topology

namespace LeanVerification.EulerSeries

open Loud

def raisedCoefficient (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (n + 1) * (n + 2) * (n + (1 : ℝ) / 2) * a n

def factoredCoefficient (a : ℕ → ℝ) : ℕ → ℝ :=
  SequenceSigns.factorCoefficient (-2)
    (SequenceSigns.factorCoefficient (-1)
      (SequenceSigns.factorCoefficient 0 (SequenceSigns.factorCoefficient (-(1 / 2)) a)))

theorem factoredCoefficient_eq (a : ℕ → ℝ) : factoredCoefficient a = raisedCoefficient a := by
  funext n
  simp only [factoredCoefficient, SequenceSigns.factorCoefficient, raisedCoefficient]
  ring

theorem raised_converges {a : ℕ → ℝ} {H : ℝ} (hH : 0 < H)
    (ha : ScalarSeries.ConvergesOn a H) : ScalarSeries.ConvergesOn (raisedCoefficient a) H := by
  rw [← factoredCoefficient_eq]
  exact (((ha.factor hH (-(1 / 2))).factor hH 0).factor hH (-1)).factor hH (-2)

theorem euler_const_add (c K : ℝ) (f : ℝ → ℝ) :
    energyEulerShift c (fun x => K + f x) = fun x => c * K + energyEulerShift c f x := by
  funext x
  simp only [energyEulerShift, deriv_const_add]
  ring

theorem euler_eqOn {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (he : EqOn f g s) (c : ℝ) :
    EqOn (energyEulerShift c f) (energyEulerShift c g) s := by
  intro x hx
  have hh : f =ᶠ[𝓝 x] g := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact he hy
  simp only [energyEulerShift, hh.deriv_eq, he hx]

theorem sum_factor_euler {a : ℕ → ℝ} {H : ℝ} (hH : 0 < H)
    (ha : ScalarSeries.ConvergesOn a H) (c : ℝ) :
    EqOn (energyEulerShift c (ScalarSeries.sum a))
      (ScalarSeries.sum (SequenceSigns.factorCoefficient (-c) a)) (Ioo (-H) H) := by
  intro x hx
  rw [ScalarSeries.sum_factor hH ha (abs_lt.mpr hx)]
  dsimp [energyEulerShift]
  ring

/-- Four actual Euler differentiations give the complete coefficient
polynomial. The constant term is eliminated by the zero shift. -/
theorem raised_euler_eq_series {a : ℕ → ℝ} {H x : ℝ} (hH : 0 < H)
    (ha : ScalarSeries.ConvergesOn a H) (K : ℝ) (hx : |x| < H) :
    energyEulerShift 2
      (energyEulerShift 1 (energyEulerShift 0
        (energyEulerShift (1 / 2) (fun v => K + ScalarSeries.sum a v)))) x =
      ScalarSeries.sum (raisedCoefficient a) x := by
  have h₀ := sum_factor_euler hH ha (1 / 2)
  have h₁ := (euler_eqOn isOpen_Ioo h₀ 0).trans
    (sum_factor_euler hH (ha.factor hH (-(1 / 2))) 0)
  simp only [neg_zero] at h₁
  have h₂ := (euler_eqOn isOpen_Ioo h₁ 1).trans
    (sum_factor_euler hH ((ha.factor hH (-(1 / 2))).factor hH 0) 1)
  have h₃ := (euler_eqOn isOpen_Ioo h₂ 2).trans
    (sum_factor_euler hH (((ha.factor hH (-(1 / 2))).factor hH 0).factor hH (-1)) 2)
  have he : energyEulerShift 0 (energyEulerShift (1 / 2)
      (fun v => K + ScalarSeries.sum a v)) =
      energyEulerShift 0 (energyEulerShift (1 / 2) (ScalarSeries.sum a)) := by
    rw [euler_const_add, euler_const_add]
    simp only [zero_mul, zero_add]
  rw [he]
  have hh := h₃ (abs_lt.mp hx)
  change energyEulerShift 2
    (energyEulerShift 1 (energyEulerShift 0 (energyEulerShift (1 / 2) (ScalarSeries.sum a)))) x =
      ScalarSeries.sum (factoredCoefficient a) x at hh
  rw [factoredCoefficient_eq] at hh
  exact hh

theorem hasSum_raised_quotient {a : ℕ → ℝ} {H x : ℝ} (hH : 0 < H)
    (ha : ScalarSeries.ConvergesOn a H) (hx : |x| < H) (hx0 : x ≠ 0) :
    HasSum (fun n : ℕ => raisedCoefficient a n * x ^ (n - 1))
      (ScalarSeries.sum (raisedCoefficient a) x / x) := by
  have he := ((raised_converges hH ha) x hx).hasSum.div_const x
  convert he using 1
  ext n
  cases n with
  | zero => simp [raisedCoefficient]
  | succ n =>
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ]
    field_simp
    ring

end LeanVerification.EulerSeries
