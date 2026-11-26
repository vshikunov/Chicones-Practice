import LeanVerification.CriticalEnergy
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact regularization of the critical-mode Green boundary

The singular jump coefficient has a weighted Wronskian that is regular
at a simple turn. The endpoint constant is calculated from the normalized
endpoint value; it is not a premise. This module also retains both energy
normalization derivatives in the rescaled Green density.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace LeanVerification.CriticalMode

def jumpNumerator (V g φ φ₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  φ x * g x + 2 * V x * φ₁ x

def jumpShape (V g φ φ₁ H : ℝ → ℝ) (x : ℝ) : ℝ :=
  jumpNumerator V g φ φ₁ x * H x ^ (-(1 : ℝ) / 3) *
    V x ^ (-(1 : ℝ) / 2) / (2 * Real.sqrt 2)

def jumpShapePrime (V g φ φ₁ H H₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (H x - jumpNumerator V g φ φ₁ x * H₁ x / (3 * H x) +
    jumpNumerator V g φ φ₁ x * g x / (2 * V x)) *
    H x ^ (-(1 : ℝ) / 3) * V x ^ (-(1 : ℝ) / 2) / (2 * Real.sqrt 2)

theorem hasDerivAt_jumpNumerator {V g φ φ₁ : ℝ → ℝ} {g₁ φ₂ x : ℝ}
    (hV : HasDerivAt V (-g x) x) (hg : HasDerivAt g g₁ x)
    (hφ : HasDerivAt φ (φ₁ x) x) (hφ₁ : HasDerivAt φ₁ φ₂ x) :
    HasDerivAt (jumpNumerator V g φ φ₁)
      (φ x * g₁ - φ₁ x * g x + 2 * V x * φ₂) x := by
  convert (hφ.mul hg).add ((hV.const_mul 2).mul hφ₁) using 1
  ring

theorem hasDerivAt_jumpShape {V g φ φ₁ H H₁ : ℝ → ℝ} {g₁ φ₂ x : ℝ}
    (hV : HasDerivAt V (-g x) x) (hg : HasDerivAt g g₁ x)
    (hφ : HasDerivAt φ (φ₁ x) x) (hφ₁ : HasDerivAt φ₁ φ₂ x)
    (hH : HasDerivAt H (H₁ x) x) (hVpos : 0 < V x) (hHpos : 0 < H x)
    (haux : H x = φ x * g₁ - φ₁ x * g x + 2 * V x * φ₂) :
    HasDerivAt (jumpShape V g φ φ₁ H) (jumpShapePrime V g φ φ₁ H H₁ x) x := by
  have hN : HasDerivAt (jumpNumerator V g φ φ₁) (H x) x := by
    rw [haux]
    exact hasDerivAt_jumpNumerator hV hg hφ hφ₁
  have hd := ((hN.mul (hH.rpow_const (p := -(1 : ℝ) / 3) (Or.inl hHpos.ne'))).mul
    (hV.rpow_const (p := -(1 : ℝ) / 2) (Or.inl hVpos.ne'))).div_const (2 * Real.sqrt 2)
  convert hd using 1
  dsimp only [jumpShapePrime]
  rw [Real.rpow_sub_one hHpos.ne', Real.rpow_sub_one hVpos.ne']
  field_simp
  ring

def regularJumpWronskian (V g φ φ₁ H H₁ U U₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  H x ^ (-(2 : ℝ) / 3) / (2 * Real.sqrt 2 * φ x) *
    (V x * (U x * H x - U x * jumpNumerator V g φ φ₁ x * H₁ x / (3 * H x) -
      U₁ x * jumpNumerator V g φ φ₁ x) +
      U x * g x * jumpNumerator V g φ φ₁ x / 2)

theorem weighted_jump_wronskian (V g φ φ₁ H H₁ U U₁ : ℝ → ℝ) (x : ℝ)
    (hV : 0 < V x) (hH : 0 < H x) (hφ : φ x ≠ 0) :
    weight V φ H x * (U x * jumpShapePrime V g φ φ₁ H H₁ x -
      U₁ x * jumpShape V g φ φ₁ H x) = regularJumpWronskian V g φ φ₁ H H₁ U U₁ x := by
  have hVp : V x ^ ((3 : ℝ) / 2) * V x ^ (-(1 : ℝ) / 2) = V x := by
    rw [← Real.rpow_add hV]
    norm_num
  have hHp : H x ^ (-(1 : ℝ) / 3) * H x ^ (-(1 : ℝ) / 3) = H x ^ (-(2 : ℝ) / 3) := by
    rw [← Real.rpow_add hH]
    congr 1
    ring
  dsimp only [weight, jumpShape, jumpShapePrime, regularJumpWronskian]
  calc
    _ = (V x ^ ((3 : ℝ) / 2) * V x ^ (-(1 : ℝ) / 2)) *
        (H x ^ (-(1 : ℝ) / 3) * H x ^ (-(1 : ℝ) / 3)) /
        (2 * Real.sqrt 2 * φ x) *
        (U x * (H x - jumpNumerator V g φ φ₁ x * H₁ x / (3 * H x) +
          jumpNumerator V g φ φ₁ x * g x / (2 * V x)) -
          U₁ x * jumpNumerator V g φ φ₁ x) := by ring
    _ = _ := by
      rw [hVp, hHp]
      field_simp [hV.ne', hH.ne', hφ]
      ring

theorem regularJumpWronskian_at_turn (V g φ φ₁ H H₁ U U₁ : ℝ → ℝ) (c : ℝ)
    (hV : V c = 0) (hH : 0 < H c) (hφ : φ c ≠ 0) (hg : g c ≠ 0)
    (hU : U c = H c ^ ((2 : ℝ) / 3) / g c ^ 2) :
    regularJumpWronskian V g φ φ₁ H H₁ U U₁ c = 1 / (4 * Real.sqrt 2) := by
  have hHp : H c ^ (-(2 : ℝ) / 3) * H c ^ ((2 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add hH]
    norm_num
  dsimp only [regularJumpWronskian, jumpNumerator]
  rw [hV, hU]
  simp only [zero_mul, add_zero, zero_add]
  calc
    _ = (H c ^ (-(2 : ℝ) / 3) * H c ^ ((2 : ℝ) / 3)) / (4 * Real.sqrt 2) := by
      field_simp [hφ, hg]
      ring
    _ = _ := by rw [hHp]

theorem continuousAt_regularJumpWronskian
    {V g φ φ₁ H H₁ U U₁ : ℝ → ℝ} {c : ℝ}
    (hV : ContinuousAt V c) (hg : ContinuousAt g c)
    (hφ : ContinuousAt φ c) (hφ₁ : ContinuousAt φ₁ c)
    (hH : ContinuousAt H c) (hH₁ : ContinuousAt H₁ c)
    (hU : ContinuousAt U c) (hU₁ : ContinuousAt U₁ c)
    (hHpos : 0 < H c) (hφ0 : φ c ≠ 0) :
    ContinuousAt (regularJumpWronskian V g φ φ₁ H H₁ U U₁) c := by
  have hN : ContinuousAt (jumpNumerator V g φ φ₁) c :=
    (hφ.mul hg).add ((continuousAt_const.mul hV).mul hφ₁)
  have hc : ContinuousAt (fun x => H x ^ (-(2 : ℝ) / 3) /
      (2 * Real.sqrt 2 * φ x)) c :=
    (hH.rpow_const (p := -(2 : ℝ) / 3) (Or.inl hHpos.ne')).div
    (continuousAt_const.mul hφ)
    (mul_ne_zero (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (by norm_num)).ne') hφ0)
  exact hc.mul ((hV.mul (((hU.mul hH).sub
    (((hU.mul hN).mul hH₁).div (continuousAt_const.mul hH)
      (mul_ne_zero (by norm_num) hHpos.ne'))).sub (hU₁.mul hN))).add
        (((hU.mul hg).mul hN).div_const 2))

theorem weighted_jump_wronskian_limit
    {V g φ φ₁ H H₁ U U₁ : ℝ → ℝ} {c : ℝ} {l : Filter ℝ}
    (hl : l ≤ 𝓝 c) (hV : ContinuousAt V c) (hg : ContinuousAt g c)
    (hφ : ContinuousAt φ c) (hφ₁ : ContinuousAt φ₁ c)
    (hH : ContinuousAt H c) (hH₁ : ContinuousAt H₁ c)
    (hU : ContinuousAt U c) (hU₁ : ContinuousAt U₁ c)
    (hV0 : V c = 0) (hHpos : 0 < H c) (hφ0 : φ c ≠ 0) (hg0 : g c ≠ 0)
    (hUval : U c = H c ^ ((2 : ℝ) / 3) / g c ^ 2)
    (hVpos : ∀ᶠ x in l, 0 < V x) :
    Tendsto (fun x => weight V φ H x *
      (U x * jumpShapePrime V g φ φ₁ H H₁ x - U₁ x * jumpShape V g φ φ₁ H x))
      l (𝓝 (1 / (4 * Real.sqrt 2))) := by
  have hc := continuousAt_regularJumpWronskian hV hg hφ hφ₁ hH hH₁ hU hU₁ hHpos hφ0
  have hv := regularJumpWronskian_at_turn V g φ φ₁ H H₁ U U₁ c hV0 hHpos hφ0 hg0 hUval
  have ht := hc.tendsto.mono_left hl
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [hVpos, (hH.eventually (Ioi_mem_nhds hHpos)).filter_mono hl,
    (hφ.eventually_ne hφ0).filter_mono hl] with x hxV hxH hxφ
  exact (weighted_jump_wronskian V g φ φ₁ H H₁ U U₁ x hxV hxH hxφ).symm

def extendedWeightEnergy (V φ H B : ℝ → ℝ) (x : ℝ) : ℝ :=
  (3 / 2 : ℝ) * V x ^ ((1 : ℝ) / 2) * H x ^ (-(1 : ℝ) / 3) / φ x -
    B x / 3 * weight V φ H x

theorem weight_energy_extension_eq (V φ H B : ℝ → ℝ) (x : ℝ)
    (hV : 0 < V x) (hφ : φ x ≠ 0) :
    (3 / (2 * V x) - B x / 3) * weight V φ H x = extendedWeightEnergy V φ H B x := by
  have hp : V x ^ ((3 : ℝ) / 2) = V x ^ ((1 : ℝ) / 2) * V x := by
    have hh := Real.rpow_add_one hV.ne' ((1 : ℝ) / 2)
    norm_num at hh
    exact hh
  dsimp only [weight, extendedWeightEnergy]
  rw [hp]
  field_simp [hV.ne', hφ]
  ring

theorem continuousAt_extendedWeightEnergy {V φ H B : ℝ → ℝ} {c : ℝ}
    (hV : ContinuousAt V c) (hφ : ContinuousAt φ c) (hH : ContinuousAt H c)
    (hB : ContinuousAt B c) (hφ0 : φ c ≠ 0) (hHpos : 0 < H c) :
    ContinuousAt (extendedWeightEnergy V φ H B) c := by
  have hr := hH.rpow_const (p := -(1 : ℝ) / 3) (Or.inl hHpos.ne')
  have hw : ContinuousAt (weight V φ H) c :=
    ((hV.rpow_const (p := (3 : ℝ) / 2) (Or.inr (by norm_num))).mul hr).div hφ hφ0
  exact (((continuousAt_const.mul
    (hV.rpow_const (p := (1 : ℝ) / 2) (Or.inr (by norm_num)))).mul hr).div hφ hφ0).sub
      ((hB.div_const 3).mul hw)

theorem extendedWeightEnergy_at_turn (V φ H B : ℝ → ℝ) (c : ℝ) (hV : V c = 0) :
    extendedWeightEnergy V φ H B c = 0 := by
  simp [extendedWeightEnergy, weight, hV, Real.zero_rpow]

theorem rescaled_wronskian_algebra (p U U₁ d d₁ c c₁ k : ℝ) :
    (k * p) * ((c * U) * (c₁ * U₁ + c * d₁) -
      (c * U₁) * (c₁ * U + c * d)) =
      k * c ^ 2 * (p * (U * d₁ - U₁ * d)) := by ring

theorem rescaled_green_density_algebra (p pL Q QL U U₁ c k k₁ : ℝ) :
    (k₁ * p + k * pL) * ((c * U₁) ^ 2 - Q * (c * U) ^ 2) -
        (k * p) * QL * (c * U) ^ 2 =
      k * c ^ 2 * (pL * (U₁ ^ 2 - Q * U ^ 2) - p * QL * U ^ 2) +
        k₁ * c ^ 2 * p * (U₁ ^ 2 - Q * U ^ 2) := by ring

end LeanVerification.CriticalMode
