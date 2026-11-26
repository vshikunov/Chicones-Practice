import LeanVerification.PositiveDCompletion.PoleCoefficientData
import Mathlib.Tactic.Positivity

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

structure LeafSigns (sgn a f rho : ℝ) : Prop where
  leaf0 : 0<upperNum00 a f rho
  leaf1 : 0<sgn*upperNum01 a f rho
  leaf2 : 0<upperNum02 a f rho
  leaf3 : 0<upperNum03 a f rho
  leaf4 : 0<upperNum04 a f rho
  leaf5 : 0<sgn*upperNum05 a f rho
  leaf6 : 0<upperNum06 a f rho
  leaf7 : 0<upperNum07 a f rho
  leaf8 : 0<upperNum08 a f rho
  leaf9 : 0<upperNum09 a f rho

structure PoleCoefficientSigns (a f rho : ℝ) : Prop where
  p4 : (sourceC a f rho)^(4 : ℕ)*phiPoleCoeff4 a f rho<0
  r0 : 0≤rxPoleCoeff0 a f rho
  r1 : 0<(sourceC a f rho)^(1 : ℕ)*rxPoleCoeff1 a f rho
  r2 : 0<(sourceC a f rho)^(2 : ℕ)*rxPoleCoeff2 a f rho
  r3 : 0<(sourceC a f rho)^(3 : ℕ)*rxPoleCoeff3 a f rho
  r4 : 0<(sourceC a f rho)^(4 : ℕ)*rxPoleCoeff4 a f rho
  r5 : 0<(sourceC a f rho)^(5 : ℕ)*rxPoleCoeff5 a f rho
  s0 : 0≤(sourceC a f rho)^(6 : ℕ)*poleComparison0 a f rho
  s1 : 0≤(sourceC a f rho)^(7 : ℕ)*poleComparison1 a f rho
  s2 : 0≤(sourceC a f rho)^(8 : ℕ)*poleComparison2 a f rho
  s3 : 0≤(sourceC a f rho)^(9 : ℕ)*poleComparison3 a f rho

theorem upper_pole_coefficient_signs {a f rho : ℝ}
    (ha : 0<a) (haf : a<f) (hf : f<1) (hr : 0<rho) (hru : rho<1)
    (h : LeafSigns 1 a f rho) : PoleCoefficientSigns a f rho := by
  have ha0 : 0<a := ha
  have hf0 : 0<f := by linarith
  have hr0 : 0<rho := hr
  have ha1 : a<1 := by linarith
  have hu : 0<1-f := by linarith
  have hg0 : 0<1-a^(2 : ℕ)*rho := by
    nlinarith [mul_lt_mul_of_pos_left hru (sq_pos_of_pos ha)]
  have hv : 0<f-a*rho := by
    nlinarith [mul_lt_mul_of_pos_left hru ha]
  have hafp : a*f<1 := by nlinarith [mul_lt_mul_of_pos_left hf ha]
  have hC : 0<sourceC a f rho := by
    unfold sourceC
    exact mul_pos (mul_pos ha hr) (by linarith)
  have hl0 := h.leaf0
  have hl1 : 0<upperNum01 a f rho := by simpa using h.leaf1
  have hl2 := h.leaf2
  have hl3 := h.leaf3
  have hl4 := h.leaf4
  have hl5 : 0<upperNum05 a f rho := by simpa using h.leaf5
  have hl6 := h.leaf6
  have hl7 := h.leaf7
  have hl8 := h.leaf8
  have hl9 := h.leaf9
  constructor
  · apply neg_pos.mp
    have he : -((sourceC a f rho)^(4 : ℕ)*phiPoleCoeff4 a f rho)=((sourceC a f rho))^(4 : ℕ)*f*a^(2 : ℕ)*rho^(2 : ℕ)*(1+a)*upperNum00 a f rho := by
      unfold phiPoleCoeff4
      ring
    rw [he]
    positivity
  · have he : rxPoleCoeff0 a f rho=3*a^(2 : ℕ)*rho^(3 : ℕ)*(1+a)^(6 : ℕ)*(1+f)^(5 : ℕ)*(1-a^(2 : ℕ)*rho)^(3 : ℕ)*(f-a*rho)^(4 : ℕ)*(poleCore00 a f rho)^(2 : ℕ)*(1-f) := by
      unfold rxPoleCoeff0
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(1 : ℕ)*rxPoleCoeff1 a f rho=(sourceC a f rho)^(1 : ℕ)*(a^(2 : ℕ)*rho^(3 : ℕ)*(1+a)^(5 : ℕ)*(1+f)^(4 : ℕ)*(1-a^(2 : ℕ)*rho)^(2 : ℕ)*(f-a*rho)^(3 : ℕ)*(1-f)*(upperNum01 a f rho)) := by
      unfold rxPoleCoeff1
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(2 : ℕ)*rxPoleCoeff2 a f rho=(sourceC a f rho)^(2 : ℕ)*(a^(2 : ℕ)*rho^(3 : ℕ)*(1+a)^(4 : ℕ)*(1+f)^(3 : ℕ)*(f-a*rho)^(2 : ℕ)*(1-f)*(1-a^(2 : ℕ)*rho)*(upperNum02 a f rho)) := by
      unfold rxPoleCoeff2
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(3 : ℕ)*rxPoleCoeff3 a f rho=(sourceC a f rho)^(3 : ℕ)*(2*a^(2 : ℕ)*rho^(3 : ℕ)*(1+a)^(3 : ℕ)*(1+f)^(2 : ℕ)*(1-f)*(1-a^(2 : ℕ)*rho)*(f-a*rho)*(upperNum03 a f rho)) := by
      unfold rxPoleCoeff3
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(4 : ℕ)*rxPoleCoeff4 a f rho=(sourceC a f rho)^(4 : ℕ)*(a^(2 : ℕ)*rho^(3 : ℕ)*(1+a)^(2 : ℕ)*(1+f)*(1-f)*(1-a^(2 : ℕ)*rho)*(upperNum04 a f rho)) := by
      unfold rxPoleCoeff4
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(5 : ℕ)*rxPoleCoeff5 a f rho=(sourceC a f rho)^(5 : ℕ)*(a^(2 : ℕ)*rho^(3 : ℕ)*(1+a)*(upperNum05 a f rho)) := by
      unfold rxPoleCoeff5
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(6 : ℕ)*poleComparison0 a f rho=(sourceC a f rho)^(6 : ℕ)*(f*a^(4 : ℕ)*rho^(5 : ℕ)*(1+a)^(5 : ℕ)*(1+f)^(3 : ℕ)*(f-a*rho)^(2 : ℕ)*(1-f)*(1-a^(2 : ℕ)*rho)*(upperNum06 a f rho)) := by
      unfold poleComparison0
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(7 : ℕ)*poleComparison1 a f rho=(sourceC a f rho)^(7 : ℕ)*(f*a^(4 : ℕ)*rho^(5 : ℕ)*(1+a)^(4 : ℕ)*(1+f)^(2 : ℕ)*(1-f)*(1-a^(2 : ℕ)*rho)*(f-a*rho)*(upperNum07 a f rho)) := by
      unfold poleComparison1
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(8 : ℕ)*poleComparison2 a f rho=(sourceC a f rho)^(8 : ℕ)*(f*a^(4 : ℕ)*rho^(5 : ℕ)*(1+a)^(3 : ℕ)*(1+f)*(1-f)*(1-a^(2 : ℕ)*rho)*(upperNum08 a f rho)) := by
      unfold poleComparison2
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(9 : ℕ)*poleComparison3 a f rho=(sourceC a f rho)^(9 : ℕ)*(2*f*a^(4 : ℕ)*rho^(5 : ℕ)*(1+a)^(3 : ℕ)*(1-f)*(upperNum09 a f rho)) := by
      unfold poleComparison3
      ring
    rw [he]
    positivity

theorem lower_pole_coefficient_signs {a f rho : ℝ}
    (ha : 1<a) (hf : 1<f) (hfa : f<a) (hr : 1<rho)
    (h : LeafSigns (-1) a f rho) : PoleCoefficientSigns a f rho := by
  have ha0 : 0<a := by linarith
  have hf0 : 0<f := by linarith
  have hr0 : 0<rho := by linarith
  have hu : 0<f-1 := by linarith
  have hg0 : 0<a^(2 : ℕ)*rho-1 := by
    nlinarith [mul_lt_mul_of_pos_left hr (sq_pos_of_pos ha0)]
  have hv : 0<a*rho-f := by
    nlinarith [mul_lt_mul_of_pos_left hr ha0]
  have hafp : 1<a*f := by nlinarith [mul_lt_mul_of_pos_left hf ha0]
  have hC : 0< -(sourceC a f rho) := by
    unfold sourceC
    exact neg_pos.mpr (mul_neg_of_pos_of_neg (mul_pos ha0 hr0) (by linarith))
  have hl0 := h.leaf0
  have hl1 : 0< -upperNum01 a f rho := by simpa using h.leaf1
  have hl2 := h.leaf2
  have hl3 := h.leaf3
  have hl4 := h.leaf4
  have hl5 : 0< -upperNum05 a f rho := by simpa using h.leaf5
  have hl6 := h.leaf6
  have hl7 := h.leaf7
  have hl8 := h.leaf8
  have hl9 := h.leaf9
  constructor
  · apply neg_pos.mp
    have he : -((sourceC a f rho)^(4 : ℕ)*phiPoleCoeff4 a f rho)=((-sourceC a f rho))^(4 : ℕ)*f*a^(2 : ℕ)*rho^(2 : ℕ)*(1+a)*upperNum00 a f rho := by
      unfold phiPoleCoeff4
      ring
    rw [he]
    positivity
  · have he : rxPoleCoeff0 a f rho=3*a^(2 : ℕ)*rho^(3 : ℕ)*(1+a)^(6 : ℕ)*(1+f)^(5 : ℕ)*(a^(2 : ℕ)*rho-1)^(3 : ℕ)*(a*rho-f)^(4 : ℕ)*(poleCore00 a f rho)^(2 : ℕ)*(f-1) := by
      unfold rxPoleCoeff0
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(1 : ℕ)*rxPoleCoeff1 a f rho=(-sourceC a f rho)^(1 : ℕ)*(a^(2 : ℕ)*rho^(3 : ℕ)*(1+a)^(5 : ℕ)*(1+f)^(4 : ℕ)*(a^(2 : ℕ)*rho-1)^(2 : ℕ)*(a*rho-f)^(3 : ℕ)*(f-1)*(-upperNum01 a f rho)) := by
      unfold rxPoleCoeff1
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(2 : ℕ)*rxPoleCoeff2 a f rho=(-sourceC a f rho)^(2 : ℕ)*(a^(2 : ℕ)*rho^(3 : ℕ)*(1+a)^(4 : ℕ)*(1+f)^(3 : ℕ)*(a*rho-f)^(2 : ℕ)*(f-1)*(a^(2 : ℕ)*rho-1)*(upperNum02 a f rho)) := by
      unfold rxPoleCoeff2
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(3 : ℕ)*rxPoleCoeff3 a f rho=(-sourceC a f rho)^(3 : ℕ)*(2*a^(2 : ℕ)*rho^(3 : ℕ)*(1+a)^(3 : ℕ)*(1+f)^(2 : ℕ)*(f-1)*(a^(2 : ℕ)*rho-1)*(a*rho-f)*(upperNum03 a f rho)) := by
      unfold rxPoleCoeff3
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(4 : ℕ)*rxPoleCoeff4 a f rho=(-sourceC a f rho)^(4 : ℕ)*(a^(2 : ℕ)*rho^(3 : ℕ)*(1+a)^(2 : ℕ)*(1+f)*(f-1)*(a^(2 : ℕ)*rho-1)*(upperNum04 a f rho)) := by
      unfold rxPoleCoeff4
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(5 : ℕ)*rxPoleCoeff5 a f rho=(-sourceC a f rho)^(5 : ℕ)*(a^(2 : ℕ)*rho^(3 : ℕ)*(1+a)*(-upperNum05 a f rho)) := by
      unfold rxPoleCoeff5
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(6 : ℕ)*poleComparison0 a f rho=(-sourceC a f rho)^(6 : ℕ)*(f*a^(4 : ℕ)*rho^(5 : ℕ)*(1+a)^(5 : ℕ)*(1+f)^(3 : ℕ)*(a*rho-f)^(2 : ℕ)*(f-1)*(a^(2 : ℕ)*rho-1)*(upperNum06 a f rho)) := by
      unfold poleComparison0
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(7 : ℕ)*poleComparison1 a f rho=(-sourceC a f rho)^(7 : ℕ)*(f*a^(4 : ℕ)*rho^(5 : ℕ)*(1+a)^(4 : ℕ)*(1+f)^(2 : ℕ)*(f-1)*(a^(2 : ℕ)*rho-1)*(a*rho-f)*(upperNum07 a f rho)) := by
      unfold poleComparison1
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(8 : ℕ)*poleComparison2 a f rho=(-sourceC a f rho)^(8 : ℕ)*(f*a^(4 : ℕ)*rho^(5 : ℕ)*(1+a)^(3 : ℕ)*(1+f)*(f-1)*(a^(2 : ℕ)*rho-1)*(upperNum08 a f rho)) := by
      unfold poleComparison2
      ring
    rw [he]
    positivity
  · have he : (sourceC a f rho)^(9 : ℕ)*poleComparison3 a f rho=(-sourceC a f rho)^(9 : ℕ)*(2*f*a^(4 : ℕ)*rho^(5 : ℕ)*(1+a)^(3 : ℕ)*(f-1)*(upperNum09 a f rho)) := by
      unfold poleComparison3
      ring
    rw [he]
    positivity

end LeanVerification.PositiveDCompletion
