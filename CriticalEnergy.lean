import LeanVerification.CriticalMode
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Energy differentiation of the actual critical-mode coefficients for a
fixed analytic potential and an energy-independent auxiliary function.
These results do not construct the flight-clock variation or its modes.
-/

noncomputable section

open Filter
open scoped Topology

namespace LeanVerification.CriticalEnergy

def jet (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ := deriv^[n] f

private theorem hasDerivAt_jet {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (n : ℕ) :
    HasDerivAt (jet f n) (jet f (n + 1) x) x := by
  simpa only [jet, Function.iterate_succ', Function.comp_apply] using
    (hf.iterated_deriv n).differentiableAt.hasDerivAt

def gap (W : ℝ → ℝ) (L x : ℝ) : ℝ := L - W x

def coefficientH (W φ : ℝ → ℝ) (L x : ℝ) : ℝ :=
  φ x * jet W 2 x - jet φ 1 x * jet W 1 x + 2 * gap W L x * jet φ 2 x

def coefficientH1 (W φ : ℝ → ℝ) (L x : ℝ) : ℝ :=
  φ x * jet W 3 x - 3 * jet W 1 x * jet φ 2 x +
    2 * gap W L x * jet φ 3 x

def coefficientH2 (W φ : ℝ → ℝ) (L x : ℝ) : ℝ :=
  jet φ 1 x * jet W 3 x + φ x * jet W 4 x -
    3 * jet W 2 x * jet φ 2 x - 5 * jet W 1 x * jet φ 3 x +
    2 * gap W L x * jet φ 4 x

theorem hasDerivAt_coefficientH {W φ : ℝ → ℝ} {L x : ℝ}
    (hW : AnalyticAt ℝ W x) (hφ : AnalyticAt ℝ φ x) :
    HasDerivAt (coefficientH W φ L) (coefficientH1 W φ L x) x := by
  have dW := hasDerivAt_jet hW 0
  have dφ := hasDerivAt_jet hφ 0
  simp only [jet, Function.iterate_zero, id_eq] at dW dφ
  have hd := ((dφ.mul (hasDerivAt_jet hW 2)).sub
    ((hasDerivAt_jet hφ 1).mul (hasDerivAt_jet hW 1))).add
      (((dW.const_sub L).const_mul 2).mul (hasDerivAt_jet hφ 2))
  convert hd using 1
  dsimp [coefficientH, coefficientH1, gap, jet]
  ring

theorem hasDerivAt_coefficientH1 {W φ : ℝ → ℝ} {L x : ℝ}
    (hW : AnalyticAt ℝ W x) (hφ : AnalyticAt ℝ φ x) :
    HasDerivAt (coefficientH1 W φ L) (coefficientH2 W φ L x) x := by
  have dW := hasDerivAt_jet hW 0
  have dφ := hasDerivAt_jet hφ 0
  simp only [jet, Function.iterate_zero, id_eq] at dW dφ
  have hd := ((dφ.mul (hasDerivAt_jet hW 3)).sub
    (((hasDerivAt_jet hW 1).const_mul 3).mul (hasDerivAt_jet hφ 2))).add
      (((dW.const_sub L).const_mul 2).mul (hasDerivAt_jet hφ 3))
  convert hd using 1
  dsimp [coefficientH1, coefficientH2, gap, jet]
  ring

theorem coefficientH_eq_auxiliary (W φ : ℝ → ℝ) (L x : ℝ) :
    coefficientH W φ L x = CriticalMode.auxiliary (gap W L)
      (jet W 1) (jet W 2) φ (jet φ 1) (jet φ 2) x := rfl

theorem hasDerivAt_coefficientH_energy (W φ : ℝ → ℝ) (L x : ℝ) :
    HasDerivAt (fun E => coefficientH W φ E x) (2 * jet φ 2 x) L := by
  convert (hasDerivAt_const L (φ x * jet W 2 x - jet φ 1 x * jet W 1 x)).add
    ((((hasDerivAt_id L).sub_const (W x)).const_mul 2).mul_const (jet φ 2 x))
    using 1
  dsimp [coefficientH, gap]
  ring

theorem hasDerivAt_coefficientH1_energy (W φ : ℝ → ℝ) (L x : ℝ) :
    HasDerivAt (fun E => coefficientH1 W φ E x) (2 * jet φ 3 x) L := by
  convert (hasDerivAt_const L (φ x * jet W 3 x - 3 * jet W 1 x * jet φ 2 x)).add
    ((((hasDerivAt_id L).sub_const (W x)).const_mul 2).mul_const (jet φ 3 x))
    using 1
  dsimp [coefficientH1, gap]
  ring

theorem hasDerivAt_coefficientH2_energy (W φ : ℝ → ℝ) (L x : ℝ) :
    HasDerivAt (fun E => coefficientH2 W φ E x) (2 * jet φ 4 x) L := by
  convert (hasDerivAt_const L
    (jet φ 1 x * jet W 3 x + φ x * jet W 4 x -
      3 * jet W 2 x * jet φ 2 x - 5 * jet W 1 x * jet φ 3 x)).add
    ((((hasDerivAt_id L).sub_const (W x)).const_mul 2).mul_const (jet φ 4 x))
    using 1
  dsimp [coefficientH2, gap]
  ring

def energyRatio (W φ : ℝ → ℝ) (L x : ℝ) : ℝ :=
  2 * jet φ 2 x / coefficientH W φ L x

def energyRatio1 (W φ : ℝ → ℝ) (L x : ℝ) : ℝ :=
  2 * jet φ 3 x / coefficientH W φ L x -
    2 * jet φ 2 x * coefficientH1 W φ L x / coefficientH W φ L x ^ 2

def energyRatio2 (W φ : ℝ → ℝ) (L x : ℝ) : ℝ :=
  2 * jet φ 4 x / coefficientH W φ L x -
    4 * jet φ 3 x * coefficientH1 W φ L x / coefficientH W φ L x ^ 2 -
    2 * jet φ 2 x * coefficientH2 W φ L x / coefficientH W φ L x ^ 2 +
    4 * jet φ 2 x * coefficientH1 W φ L x ^ 2 / coefficientH W φ L x ^ 3

theorem hasDerivAt_energyRatio {W φ : ℝ → ℝ} {L x : ℝ}
    (hW : AnalyticAt ℝ W x) (hφ : AnalyticAt ℝ φ x)
    (hH : coefficientH W φ L x ≠ 0) :
    HasDerivAt (energyRatio W φ L) (energyRatio1 W φ L x) x := by
  have hd := ((hasDerivAt_jet hφ 2).const_mul 2).div
    (hasDerivAt_coefficientH hW hφ) hH
  convert hd using 1
  dsimp [energyRatio1]
  field_simp
  ring

theorem hasDerivAt_energyRatio1 {W φ : ℝ → ℝ} {L x : ℝ}
    (hW : AnalyticAt ℝ W x) (hφ : AnalyticAt ℝ φ x)
    (hH : coefficientH W φ L x ≠ 0) :
    HasDerivAt (energyRatio1 W φ L) (energyRatio2 W φ L x) x := by
  have dH := hasDerivAt_coefficientH (L := L) hW hφ
  have dH1 := hasDerivAt_coefficientH1 (L := L) hW hφ
  have hd := (((hasDerivAt_jet hφ 3).const_mul 2).div dH hH).sub
    ((((hasDerivAt_jet hφ 2).const_mul 2).mul dH1).div (dH.pow 2) (pow_ne_zero 2 hH))
  convert hd using 1
  dsimp [energyRatio2]
  field_simp
  ring

def coefficientQ (W φ : ℝ → ℝ) (L : ℝ) : ℝ → ℝ :=
  CriticalMode.curvature (coefficientH W φ L) (coefficientH1 W φ L)
    (coefficientH2 W φ L) φ (jet φ 1) (jet φ 2)

theorem coefficientQ_eq_spatial_derivatives {W φ : ℝ → ℝ} {L x : ℝ}
    (hW : AnalyticAt ℝ W x) (hφ : AnalyticAt ℝ φ x) :
    coefficientQ W φ L x =
      deriv (deriv (coefficientH W φ L)) x / (3 * coefficientH W φ L x) -
        5 * (deriv (coefficientH W φ L) x) ^ 2 / (9 * coefficientH W φ L x ^ 2) -
        deriv φ x * deriv (coefficientH W φ L) x / (3 * φ x * coefficientH W φ L x) +
        deriv (deriv φ) x / φ x := by
  have h1 := (hasDerivAt_coefficientH (L := L) hW hφ).deriv
  have heq : deriv (coefficientH W φ L) =ᶠ[𝓝 x] coefficientH1 W φ L := by
    filter_upwards [hW.eventually_analyticAt, hφ.eventually_analyticAt] with y hyW hyφ
    exact (hasDerivAt_coefficientH (L := L) hyW hyφ).deriv
  have h2 : deriv (deriv (coefficientH W φ L)) x = coefficientH2 W φ L x :=
    heq.deriv_eq.trans (hasDerivAt_coefficientH1 hW hφ).deriv
  rw [h1, h2]
  rfl

theorem hasDerivAt_coefficientQ_energy {W φ : ℝ → ℝ} {L x : ℝ}
    (hH : coefficientH W φ L x ≠ 0) (hφ : φ x ≠ 0) :
    HasDerivAt (fun E => coefficientQ W φ E x)
      (energyRatio2 W φ L x / 3 -
        (4 * coefficientH1 W φ L x / (9 * coefficientH W φ L x) +
          jet φ 1 x / (3 * φ x)) * energyRatio1 W φ L x) L := by
  have dH := hasDerivAt_coefficientH_energy W φ L x
  have dH1 := hasDerivAt_coefficientH1_energy W φ L x
  have dH2 := hasDerivAt_coefficientH2_energy W φ L x
  have hd := (((dH2.div (dH.const_mul 3) (mul_ne_zero (by norm_num) hH)).sub
    (((dH1.pow 2).const_mul 5).div ((dH.pow 2).const_mul 9)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hH)))).sub
    ((dH1.const_mul (jet φ 1 x)).div (dH.const_mul (3 * φ x))
      (mul_ne_zero (mul_ne_zero (by norm_num) hφ) hH))).add_const (jet φ 2 x / φ x)
  convert hd using 1
  dsimp [energyRatio2, energyRatio1]
  field_simp
  ring

/-- The displayed energy derivative uses actual spatial derivatives of
`B = 2 φ'' / H`, with their quotient-rule conditions discharged. -/
theorem hasDerivAt_coefficientQ_energy_spatial {W φ : ℝ → ℝ} {L x : ℝ}
    (hW : AnalyticAt ℝ W x) (hφa : AnalyticAt ℝ φ x)
    (hH : coefficientH W φ L x ≠ 0) (hφ : φ x ≠ 0) :
    HasDerivAt (fun E => coefficientQ W φ E x)
      (deriv (deriv (energyRatio W φ L)) x / 3 -
        (4 * deriv (coefficientH W φ L) x / (9 * coefficientH W φ L x) +
          deriv φ x / (3 * φ x)) * deriv (energyRatio W φ L) x) L := by
  have heq : deriv (energyRatio W φ L) =ᶠ[𝓝 x] energyRatio1 W φ L := by
    filter_upwards [hW.eventually_analyticAt, hφa.eventually_analyticAt,
      (hasDerivAt_coefficientH (L := L) hW hφa).continuousAt.eventually_ne hH]
      with y hyW hyφ hyH
    exact (hasDerivAt_energyRatio hyW hyφ hyH).deriv
  have h2 : deriv (deriv (energyRatio W φ L)) x = energyRatio2 W φ L x :=
    heq.deriv_eq.trans (hasDerivAt_energyRatio1 hW hφa hH).deriv
  rw [h2, (hasDerivAt_energyRatio hW hφa hH).deriv,
    (hasDerivAt_coefficientH hW hφa).deriv]
  exact hasDerivAt_coefficientQ_energy hH hφ

def coefficientP (W φ : ℝ → ℝ) (L : ℝ) : ℝ → ℝ :=
  CriticalMode.weight (gap W L) φ (coefficientH W φ L)

theorem hasDerivAt_coefficientP_energy {W φ : ℝ → ℝ} {L x : ℝ}
    (hV : 0 < gap W L x) (hH : 0 < coefficientH W φ L x) (hφ : φ x ≠ 0) :
    HasDerivAt (fun E => coefficientP W φ E x)
      ((3 / (2 * gap W L x) - energyRatio W φ L x / 3) * coefficientP W φ L x) L := by
  have dV : HasDerivAt (fun E => gap W E x) 1 L := by
    simpa only [gap, sub_zero] using (hasDerivAt_id L).sub_const (W x)
  have dH := hasDerivAt_coefficientH_energy W φ L x
  have hd := ((dV.rpow_const (p := (3 : ℝ) / 2) (Or.inl (ne_of_gt hV))).mul
    (dH.rpow_const (p := -(1 : ℝ) / 3) (Or.inl (ne_of_gt hH)))).div_const (φ x)
  convert hd using 1
  dsimp [coefficientP, CriticalMode.weight, energyRatio]
  rw [Real.rpow_sub_one (ne_of_gt hV), Real.rpow_sub_one (ne_of_gt hH)]
  field_simp [hφ]
  ring

end LeanVerification.CriticalEnergy
