import LeanVerification.PairedCoefficients

/-!
# Actual spatial normalizations of the paired critical mode

Both spatially constant factors are retained explicitly. Their product
in the Green boundary is exactly 2(S-h).
-/

noncomputable section

open Set Filter
open scoped Topology

namespace LeanVerification.PairedMode

set_option maxHeartbeats 1400000

def weightScale (S h : ℝ) : ℝ := ((S - h) / 2) ^ ((1 : ℝ) / 3)

def modeScale (S h : ℝ) : ℝ := 2 * weightScale S h

theorem weightScale_pos {S h : ℝ} (hδ : h < S) : 0 < weightScale S h :=
  Real.rpow_pos_of_pos (div_pos (sub_pos.mpr hδ) (by norm_num)) _

theorem modeScale_pos {S h : ℝ} (hδ : h < S) : 0 < modeScale S h :=
  mul_pos (by norm_num) (weightScale_pos hδ)

theorem weightScale_cube {S h : ℝ} (hδ : h < S) : weightScale S h ^ 3 = (S - h) / 2 := by
  dsimp only [weightScale]
  rw [← Real.rpow_mul_natCast (div_nonneg (sub_pos.mpr hδ).le (by norm_num))]
  norm_num

theorem normalization_product {S h : ℝ} (hδ : h < S) :
    weightScale S h * modeScale S h ^ 2 = 2 * (S - h) := by
  dsimp only [modeScale]
  nlinarith [weightScale_cube hδ]

theorem normalized_auxiliary_power {W : ℝ → ℝ} {S h x : ℝ}
    (hW : AnalyticAt ℝ W x) (hSigma : 0 < sigma W S x)
    (hδ : h < S) (hA : 0 < denominator W S x) :
    weightScale S h * CriticalEnergy.coefficientH W (auxiliary W S) h x ^ (-(1 : ℝ) / 3) =
      auxiliary W S x * denominator W S x ^ (-(1 : ℝ) / 3) := by
  have hs : 0 < auxiliary W S x := Real.sqrt_pos.mpr hSigma
  have hd : 0 < (S - h) / 2 := div_pos (sub_pos.mpr hδ) (by norm_num)
  have hH : CriticalEnergy.coefficientH W (auxiliary W S) h x =
      ((S - h) / 2 * denominator W S x) / auxiliary W S x ^ 3 := by
    rw [coefficientH_eq hW hSigma]
    ring
  have hp : (auxiliary W S x ^ 3) ^ (-(1 : ℝ) / 3) = (auxiliary W S x)⁻¹ := by
    rw [← Real.rpow_natCast_mul hs.le]
    norm_num [Real.rpow_neg_one]
  rw [hH, Real.div_rpow (mul_pos hd hA).le (pow_pos hs 3).le,
    Real.mul_rpow hd.le hA.le, hp]
  dsimp only [weightScale]
  have hn : ((S - h) / 2) ^ (-(1 : ℝ) / 3) =
      (((S - h) / 2) ^ ((1 : ℝ) / 3))⁻¹ := by
    rw [show -(1 : ℝ) / 3 = -((1 : ℝ) / 3) by ring, Real.rpow_neg hd.le]
  rw [hn]
  field_simp
  ring

theorem normalized_weight {W : ℝ → ℝ} {S h x : ℝ}
    (hW : AnalyticAt ℝ W x) (hSigma : 0 < sigma W S x)
    (hδ : h < S) (hA : 0 < denominator W S x) :
    weightScale S h * CriticalEnergy.coefficientP W (auxiliary W S) h x =
      (h - W x) ^ ((3 : ℝ) / 2) * denominator W S x ^ (-(1 : ℝ) / 3) := by
  have hs : auxiliary W S x ≠ 0 := (Real.sqrt_pos.mpr hSigma).ne'
  have hp := normalized_auxiliary_power hW hSigma hδ hA
  dsimp only [CriticalEnergy.coefficientP, CriticalMode.weight, CriticalEnergy.gap]
  calc
    _ = (h - W x) ^ ((3 : ℝ) / 2) *
        (weightScale S h * CriticalEnergy.coefficientH W (auxiliary W S) h x ^ (-(1 : ℝ) / 3)) /
        auxiliary W S x := by ring
    _ = _ := by rw [hp]; field_simp; ring

theorem normalized_mode {W Y : ℝ → ℝ} {S h x : ℝ}
    (hW : AnalyticAt ℝ W x) (hSigma : 0 < sigma W S x)
    (hδ : h < S) (hA : 0 < denominator W S x)
    (hY : 2 * (h - W x) * deriv Y x + deriv W x * Y x = 1) :
    modeScale S h * CriticalMode.mode
      (CriticalMode.bracket (auxiliary W S) (deriv (auxiliary W S)) Y (deriv Y))
      (CriticalEnergy.coefficientH W (auxiliary W S) h) x =
        (1 + 2 * (S - h) * deriv Y x) * denominator W S x ^ (-(1 : ℝ) / 3) := by
  have hs : auxiliary W S x ≠ 0 := (Real.sqrt_pos.mpr hSigma).ne'
  have hsq : auxiliary W S x ^ 2 = S - W x := Real.sq_sqrt hSigma.le
  have hφd := (hasDerivAt_auxiliary hW hSigma).deriv
  have hp := normalized_auxiliary_power hW hSigma hδ hA
  dsimp only [modeScale, CriticalMode.mode, CriticalMode.bracket]
  rw [hφd]
  calc
    _ = (2 * auxiliary W S x * deriv Y x + deriv W x * Y x / auxiliary W S x) *
        (weightScale S h * CriticalEnergy.coefficientH W (auxiliary W S) h x ^ (-(1 : ℝ) / 3)) := by ring
    _ = _ := by
      rw [hp]
      field_simp
      have hZ : 2 * auxiliary W S x ^ 2 * deriv Y x + deriv W x * Y x =
          1 + 2 * (S - h) * deriv Y x := by
        linear_combination hY + 2 * deriv Y x * hsq
      linear_combination (auxiliary W S x * denominator W S x ^ (-(1 : ℝ) / 3)) * hZ

theorem green_density_normalization (δ d c s Hp Ap v p u u₁ q : ℝ)
    (hδ : δ ≠ 0) (hs : s ≠ 0) (hp : d * Hp = s * Ap) (hc : d * c ^ 2 = 2 * δ) :
    3 * (v * Ap * ((c * u₁) ^ 2 - q * (c * u) ^ 2)) =
      4 * δ * (((3 : ℝ) / 2 * v * Hp / s + p / (3 * δ)) * (u₁ ^ 2 - q * u ^ 2)) -
        (4 : ℝ) / 3 * (p * (u₁ ^ 2 - q * u ^ 2)) := by
  have hcoef : c ^ 2 * Ap = 2 * δ * Hp / s := by
    apply (eq_div_iff hs).2
    linear_combination -(c ^ 2) * hp + Hp * hc
  calc
    _ = 3 * v * (c ^ 2 * Ap) * (u₁ ^ 2 - q * u ^ 2) := by ring
    _ = _ := by rw [hcoef]; field_simp; ring

theorem modeScale_at_turn {W : ℝ → ℝ} {S h x : ℝ}
    (hW : AnalyticAt ℝ W x) (hδ : h < S) (hA : 0 < denominator W S x) (hturn : W x = h) :
    modeScale S h * CriticalEnergy.coefficientH W (auxiliary W S) h x ^ ((2 : ℝ) / 3) =
      denominator W S x ^ ((2 : ℝ) / 3) := by
  have hSigma : 0 < sigma W S x := by dsimp only [sigma]; rw [hturn]; exact sub_pos.mpr hδ
  have hs : 0 < auxiliary W S x := Real.sqrt_pos.mpr hSigma
  have hsq : auxiliary W S x ^ 2 = S - h := by
    calc
      _ = sigma W S x := Real.sq_sqrt hSigma.le
      _ = S - h := by rw [sigma, hturn]
  have hH := coefficientH_pos hW hSigma hδ hA
  have hp := normalized_auxiliary_power hW hSigma hδ hA
  have hpowerH : CriticalEnergy.coefficientH W (auxiliary W S) h x ^ ((2 : ℝ) / 3) =
      CriticalEnergy.coefficientH W (auxiliary W S) h x *
        CriticalEnergy.coefficientH W (auxiliary W S) h x ^ (-(1 : ℝ) / 3) := by
    rw [show (2 : ℝ) / 3 = 1 + (-(1 : ℝ) / 3) by ring, Real.rpow_add hH, Real.rpow_one]
  have hpowerA : denominator W S x ^ ((2 : ℝ) / 3) =
      denominator W S x * denominator W S x ^ (-(1 : ℝ) / 3) := by
    rw [show (2 : ℝ) / 3 = 1 + (-(1 : ℝ) / 3) by ring, Real.rpow_add hA, Real.rpow_one]
  have hAH : 2 * auxiliary W S x * CriticalEnergy.coefficientH W (auxiliary W S) h x =
      denominator W S x := by
    rw [coefficientH_eq hW hSigma, ← hsq]
    field_simp
    ring
  rw [hpowerH, hpowerA]
  dsimp only [modeScale]
  calc
    _ = (2 * auxiliary W S x * CriticalEnergy.coefficientH W (auxiliary W S) h x) *
        denominator W S x ^ (-(1 : ℝ) / 3) := by linear_combination 2 * CriticalEnergy.coefficientH W (auxiliary W S) h x * hp
    _ = _ := by rw [hAH]

theorem primitive_derivative_algebra (v s A u u₁ q g : ℝ) (hs : s ≠ 0) (hsq : s ^ 2 = v) :
    ((u₁ * (v * s * A * u₁) + u * (-(v * s * A) * q * u)) * v -
      (u * (v * s * A * u₁)) * (-g)) / v ^ 2 =
        s * A * (u₁ ^ 2 - q * u ^ 2) + g * u * A * (u₁ / s) := by
  rw [← hsq]
  field_simp
  ring

end LeanVerification.PairedMode
