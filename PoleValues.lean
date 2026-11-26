import LeanVerification.PositiveDCompletion.SourceNumerators
import LeanVerification.PositiveDCompletion.PolePolynomialAlgebra
import LeanVerification.PositiveDCompletion.PoleSigns
import LeanVerification.PositiveDCompletion.PhiPoleCoefficient0
import LeanVerification.PositiveDCompletion.PhiPoleCoefficient1
import LeanVerification.PositiveDCompletion.PhiPoleCoefficient2
import LeanVerification.PositiveDCompletion.PhiPoleCoefficient3
import LeanVerification.PositiveDCompletion.PhiPoleCoefficient4
import LeanVerification.PositiveDCompletion.RxPoleCoefficient0
import LeanVerification.PositiveDCompletion.RxPoleCoefficient1
import LeanVerification.PositiveDCompletion.RxPoleCoefficient2
import LeanVerification.PositiveDCompletion.RxPoleCoefficient3
import LeanVerification.PositiveDCompletion.RxPoleCoefficient4
import LeanVerification.PositiveDCompletion.RxPoleCoefficient5
import LeanVerification.PositiveDCompletion.RxPoleCoefficient6
import LeanVerification.PositiveDCompletion.PoleComparison0
import LeanVerification.PositiveDCompletion.PoleComparison1
import LeanVerification.PositiveDCompletion.PoleComparison2
import LeanVerification.PositiveDCompletion.PoleComparison3

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

def phiPoleValue (a f rho n : ℝ) : ℝ :=
  quarticValue ((sourceC a f rho)^(0 : ℕ)*phiPoleCoeff0 a f rho) ((sourceC a f rho)^(1 : ℕ)*phiPoleCoeff1 a f rho) ((sourceC a f rho)^(2 : ℕ)*phiPoleCoeff2 a f rho) ((sourceC a f rho)^(3 : ℕ)*phiPoleCoeff3 a f rho) ((sourceC a f rho)^(4 : ℕ)*phiPoleCoeff4 a f rho) n

theorem phiPoleValue_scaled (a f rho n : ℝ) :
    phiPoleValue a f rho n=quarticValue (phiPoleCoeff0 a f rho) (phiPoleCoeff1 a f rho) (phiPoleCoeff2 a f rho) (phiPoleCoeff3 a f rho) (phiPoleCoeff4 a f rho) (sourceC a f rho*n) := by
  unfold phiPoleValue quarticValue
  ring

theorem phi_pole_numerator (a f rho w : ℝ) :
    quarticValue (phiPoleCoeff0 a f rho) (phiPoleCoeff1 a f rho) (phiPoleCoeff2 a f rho) (phiPoleCoeff3 a f rho) (phiPoleCoeff4 a f rho) (-transportN a f rho w)=
      (sourceC a f rho)^(4 : ℕ)*phiNumerator a f rho w := by
  have he := inverse_homogeneous_4 (sourceBase a f rho) (sourceC a f rho) w
    (phiNumCoeff0 a f rho) (phiNumCoeff1 a f rho) (phiNumCoeff2 a f rho) (phiNumCoeff3 a f rho) (phiNumCoeff4 a f rho)
  rw [←phi_pole_coefficient_0,←phi_pole_coefficient_1,←phi_pole_coefficient_2,←phi_pole_coefficient_3,←phi_pole_coefficient_4] at he
  have hN : -sourceBase a f rho-sourceC a f rho*w= -transportN a f rho w := by
    rw [transportN_source]
    ring
  rw [hN] at he
  convert he.symm using 1 <;>
    simp only [quarticValue,phiNumerator,pow_zero,pow_one,mul_one] <;> ring

theorem phiPoleValue_actual {a f rho w : ℝ} (hc : sourceC a f rho≠0) :
    phiPoleValue a f rho (-transportN a f rho w/sourceC a f rho)=
      (sourceC a f rho)^(4 : ℕ)*phiNumerator a f rho w := by
  rw [phiPoleValue_scaled,mul_div_cancel₀ _ hc,phi_pole_numerator]

def rxPoleValue (a f rho n : ℝ) : ℝ :=
  sexticValue ((sourceC a f rho)^(0 : ℕ)*rxPoleCoeff0 a f rho) ((sourceC a f rho)^(1 : ℕ)*rxPoleCoeff1 a f rho) ((sourceC a f rho)^(2 : ℕ)*rxPoleCoeff2 a f rho) ((sourceC a f rho)^(3 : ℕ)*rxPoleCoeff3 a f rho) ((sourceC a f rho)^(4 : ℕ)*rxPoleCoeff4 a f rho) ((sourceC a f rho)^(5 : ℕ)*rxPoleCoeff5 a f rho) ((sourceC a f rho)^(6 : ℕ)*rxPoleCoeff6 a f rho) n

theorem rxPoleValue_scaled (a f rho n : ℝ) :
    rxPoleValue a f rho n=sexticValue (rxPoleCoeff0 a f rho) (rxPoleCoeff1 a f rho) (rxPoleCoeff2 a f rho) (rxPoleCoeff3 a f rho) (rxPoleCoeff4 a f rho) (rxPoleCoeff5 a f rho) (rxPoleCoeff6 a f rho) (sourceC a f rho*n) := by
  unfold rxPoleValue sexticValue
  ring

theorem rx_pole_numerator (a f rho w : ℝ) :
    sexticValue (rxPoleCoeff0 a f rho) (rxPoleCoeff1 a f rho) (rxPoleCoeff2 a f rho) (rxPoleCoeff3 a f rho) (rxPoleCoeff4 a f rho) (rxPoleCoeff5 a f rho) (rxPoleCoeff6 a f rho) (-transportN a f rho w)=
      (sourceC a f rho)^(6 : ℕ)*rxNumerator a f rho w := by
  have he := inverse_homogeneous_6 (sourceBase a f rho) (sourceC a f rho) w
    (rxNumCoeff0 a f rho) (rxNumCoeff1 a f rho) (rxNumCoeff2 a f rho) (rxNumCoeff3 a f rho) (rxNumCoeff4 a f rho) (rxNumCoeff5 a f rho) (rxNumCoeff6 a f rho)
  rw [←rx_pole_coefficient_0,←rx_pole_coefficient_1,←rx_pole_coefficient_2,←rx_pole_coefficient_3,←rx_pole_coefficient_4,←rx_pole_coefficient_5,←rx_pole_coefficient_6] at he
  have hN : -sourceBase a f rho-sourceC a f rho*w= -transportN a f rho w := by
    rw [transportN_source]
    ring
  rw [hN] at he
  convert he.symm using 1 <;>
    simp only [sexticValue,rxNumerator,pow_zero,pow_one,mul_one] <;> ring

theorem rxPoleValue_actual {a f rho w : ℝ} (hc : sourceC a f rho≠0) :
    rxPoleValue a f rho (-transportN a f rho w/sourceC a f rho)=
      (sourceC a f rho)^(6 : ℕ)*rxNumerator a f rho w := by
  rw [rxPoleValue_scaled,mul_div_cancel₀ _ hc,rx_pole_numerator]

theorem scaled_pole_comparison_0 (a f rho : ℝ) :
    -((sourceC a f rho)^(4 : ℕ)*phiPoleCoeff4 a f rho)*((sourceC a f rho)^(2 : ℕ)*rxPoleCoeff2 a f rho)+
      ((sourceC a f rho)^(6 : ℕ)*rxPoleCoeff6 a f rho)*((sourceC a f rho)^(0 : ℕ)*phiPoleCoeff0 a f rho)=
      (sourceC a f rho)^(6 : ℕ)*poleComparison0 a f rho := by
  rw [←pole_comparison_identity_0]
  ring

theorem scaled_pole_comparison_1 (a f rho : ℝ) :
    -((sourceC a f rho)^(4 : ℕ)*phiPoleCoeff4 a f rho)*((sourceC a f rho)^(3 : ℕ)*rxPoleCoeff3 a f rho)+
      ((sourceC a f rho)^(6 : ℕ)*rxPoleCoeff6 a f rho)*((sourceC a f rho)^(1 : ℕ)*phiPoleCoeff1 a f rho)=
      (sourceC a f rho)^(7 : ℕ)*poleComparison1 a f rho := by
  rw [←pole_comparison_identity_1]
  ring

theorem scaled_pole_comparison_2 (a f rho : ℝ) :
    -((sourceC a f rho)^(4 : ℕ)*phiPoleCoeff4 a f rho)*((sourceC a f rho)^(4 : ℕ)*rxPoleCoeff4 a f rho)+
      ((sourceC a f rho)^(6 : ℕ)*rxPoleCoeff6 a f rho)*((sourceC a f rho)^(2 : ℕ)*phiPoleCoeff2 a f rho)=
      (sourceC a f rho)^(8 : ℕ)*poleComparison2 a f rho := by
  rw [←pole_comparison_identity_2]
  ring

theorem scaled_pole_comparison_3 (a f rho : ℝ) :
    -((sourceC a f rho)^(4 : ℕ)*phiPoleCoeff4 a f rho)*((sourceC a f rho)^(5 : ℕ)*rxPoleCoeff5 a f rho)+
      ((sourceC a f rho)^(6 : ℕ)*rxPoleCoeff6 a f rho)*((sourceC a f rho)^(3 : ℕ)*phiPoleCoeff3 a f rho)=
      (sourceC a f rho)^(9 : ℕ)*poleComparison3 a f rho := by
  rw [←pole_comparison_identity_3]
  ring

theorem rx_numerator_pos_of_phi_pos {a f rho w : ℝ}
    (hc : sourceC a f rho≠0) (hn : 0< -transportN a f rho w/sourceC a f rho)
    (hs : PoleCoefficientSigns a f rho) (hp : 0<phiNumerator a f rho w) :
    0<rxNumerator a f rho w := by
  have hC4 : 0<(sourceC a f rho)^(4 : ℕ) := by positivity
  have hC6 : 0<(sourceC a f rho)^(6 : ℕ) := by positivity
  have hPhi : 0<phiPoleValue a f rho (-transportN a f rho w/sourceC a f rho) := by
    rw [phiPoleValue_actual hc]
    exact mul_pos hC4 hp
  have hR : 0<rxPoleValue a f rho (-transportN a f rho w/sourceC a f rho) := by
    apply sextic_pos_of_quartic_pos hn hs.p4 (by simpa only [pow_zero,one_mul] using hs.r0)
      hs.r1 hs.r2.le hs.r3.le hs.r4.le hs.r5.le
    · rw [scaled_pole_comparison_0]
      exact hs.s0
    · rw [scaled_pole_comparison_1]
      exact hs.s1
    · rw [scaled_pole_comparison_2]
      exact hs.s2
    · rw [scaled_pole_comparison_3]
      exact hs.s3
    · exact hPhi
  rw [rxPoleValue_actual hc] at hR
  exact pos_of_mul_pos_right hR hC6.le

theorem modelRX_pos_of_pole_signs {a f rho w : ℝ}
    (h : SignedRegular a f rho) (hc : sourceC a f rho≠0)
    (hn : 0< -transportN a f rho w/sourceC a f rho)
    (hN : transportN a f rho w≠0) (hW : 1+w≠0)
    (hdenP : 0<4*(1+w)*modelA a f rho*(transportN a f rho w)^(3 : ℕ))
    (hdenR : 0<4*a*(1+f)*(1+w)*modelA a f rho*(transportN a f rho w)^(5 : ℕ))
    (hs : PoleCoefficientSigns a f rho) (hp : 0<modelF a f rho w) :
    0<modelF a f rho w*modelR a f rho w := by
  have hPsi : modelPsi a f rho w≠0 := by
    intro he
    have hz : modelF a f rho w=0 := by rw [modelF,he,mul_zero,zero_div]
    rw [hz] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  have hnum : 0<phiNumerator a f rho w := by
    rw [h.modelF_eq_phiNumerator hW hN] at hp
    exact (div_pos_iff_of_pos_right hdenP).mp hp
  have hR := rx_numerator_pos_of_phi_pos hc hn hs hnum
  rw [h.modelRX_eq_rxNumerator hW hN hPsi]
  exact div_pos hR hdenR

end LeanVerification.PositiveDCompletion
