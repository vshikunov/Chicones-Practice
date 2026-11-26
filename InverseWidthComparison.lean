import LeanVerification.InverseDerivativeJets
import LeanVerification.LowerAlgebra

/-! Inverse-width curvature transfer using actual derivatives of mutually inverse functions. -/

noncomputable section
open Filter
open scoped Topology

namespace LeanVerification.InverseWidthComparison

set_option maxHeartbeats 1000000

def widthQ (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  -f h / 4 + h * deriv f h + h ^ 2 * deriv (deriv f) h

theorem deriv_widthQ {f : ℝ → ℝ} {h : ℝ} (hf : AnalyticAt ℝ f h) :
    deriv (widthQ f) h =
      (3 / 4 : ℝ) * deriv f h + 3 * h * deriv (deriv f) h +
        h ^ 2 * deriv (deriv (deriv f)) h := by
  have hf0 := hf.differentiableAt.hasDerivAt
  have hf1 := hf.deriv.differentiableAt.hasDerivAt
  have hf2 := hf.deriv.deriv.differentiableAt.hasDerivAt
  have hd := ((hf0.neg.div_const 4).add ((hasDerivAt_id h).mul hf1)).add
    (((hasDerivAt_id h).pow 2).mul hf2)
  convert hd.deriv using 1 <;> simp only [widthQ, id_eq] <;> ring

theorem normalized_parameters {w w1 w2 w3 h : ℝ}
    (hh : h ≠ 0) (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0) :
    (w / 4) * (-h ^ 2 * w2) / (h * w1) ^ 2 =
        w * (-w2 / w1 ^ 3) / (4 * (1 / w1)) ∧
    (h * w1) * (h ^ 3 * w3) / (-h ^ 2 * w2) ^ 2 =
        3 - (1 / w1) * ((3 * w2 ^ 2 - w1 * w3) / w1 ^ 5) /
          (-w2 / w1 ^ 3) ^ 2 := by
  constructor <;> field_simp <;> ring

/-- The comparison is assumed only where its actual inverse-width coefficient is positive.
All inverse derivative identities and the Euler derivative of Q are proved here. -/
theorem curvature_transfer {f e : ℝ → ℝ} {h : ℝ}
    (hf : AnalyticAt ℝ f h) (he : AnalyticAt ℝ e (f h))
    (hinv : (fun x => e (f x)) =ᶠ[𝓝 h] id)
    (hh : 0 < h) (hw : 0 < f h) (hw1 : 0 < deriv f h)
    (hw2 : deriv (deriv f) h < 0)
    (hcomp : 0 < 1 - f h * deriv (deriv e) (f h) / deriv e (f h) →
      deriv e (f h) ^ 2 * deriv (deriv (deriv e)) (f h) ≤
        (1 / 2 : ℝ) * deriv (deriv e) (f h) ^ 2 *
          (deriv e (f h) - f h * deriv (deriv e) (f h)))
    (hQ : 0 < widthQ f h) :
    0 < h * deriv (widthQ f) h + (1 / 2 : ℝ) * widthQ f h := by
  let A := f h / 4
  let B := h * deriv f h
  let C := -h ^ 2 * deriv (deriv f) h
  let E3 := h ^ 3 * deriv (deriv (deriv f)) h
  have hA : 0 < A := div_pos hw (by norm_num)
  have hB : 0 < B := mul_pos hh hw1
  have hC : 0 < C := mul_pos_of_neg_of_neg (neg_neg_of_pos (sq_pos_of_pos hh)) hw2
  have hq : 0 < -A + B - C := by
    convert hQ using 1 <;> dsimp [A, B, C, widthQ] <;> ring
  have hmu : 0 < A * C / B ^ 2 := div_pos (mul_pos hA hC) (sq_pos_of_pos hB)
  have hid : C / B - (C / B) ^ 2 - A * C / B ^ 2 =
      (C / B ^ 2) * (-A + B - C) := by field_simp; ring
  have hupper : A * C / B ^ 2 < C / B - (C / B) ^ 2 := by
    apply sub_pos.mp
    rw [hid]
    exact mul_pos (div_pos hC (sq_pos_of_pos hB)) hq
  have hchi0 := (LowerAlgebra.admissible_bounds (C / B) (A * C / B ^ 2) hmu hupper).2.2.2
  have he1 := InverseDerivativeJets.first hf he hinv hw1.ne'
  have he2 := InverseDerivativeJets.second hf he hinv hw1.ne'
  have he3 := InverseDerivativeJets.third hf he hinv hw1.ne'
  have hep1 : 0 < deriv e (f h) := by rw [he1]; positivity
  have hep2 : 0 < deriv (deriv e) (f h) := by
    rw [he2]
    exact div_pos (neg_pos.mpr hw2) (pow_pos hw1 3)
  obtain ⟨hmu_id, hdelta_id⟩ := normalized_parameters (w := f h) (w1 := deriv f h)
    (w2 := deriv (deriv f) h) (w3 := deriv (deriv (deriv f)) h) hh.ne' hw1.ne' hw2.ne
  have hmu_eq : A * C / B ^ 2 = f h * deriv (deriv e) (f h) / (4 * deriv e (f h)) := by
    rw [he1, he2]
    exact hmu_id
  have hdelta_eq : B * E3 / C ^ 2 =
      3 - deriv e (f h) * deriv (deriv (deriv e)) (f h) / deriv (deriv e) (f h) ^ 2 := by
    rw [he1, he2, he3]
    exact hdelta_id
  have hchi : 0 < 1 - f h * deriv (deriv e) (f h) / deriv e (f h) := by
    rw [hmu_eq] at hchi0
    convert hchi0 using 1 <;> ring
  have hratio := LowerAlgebra.ratio_bound_from_inverse_derivative_comparison
    (f h) (deriv e (f h)) (deriv (deriv e) (f h)) (deriv (deriv (deriv e)) (f h))
    hep1 hep2 (hcomp hchi)
  rw [← hmu_eq, ← hdelta_eq] at hratio
  have hpos := LowerAlgebra.unnormalizedCurvature_pos_of_ratio_bound A B C 1 E3
    hA hB hC (by simpa using hq) hratio
  rw [deriv_widthQ hf]
  convert hpos using 1 <;> simp only [A, B, C, E3, widthQ] <;> ring

end LeanVerification.InverseWidthComparison
