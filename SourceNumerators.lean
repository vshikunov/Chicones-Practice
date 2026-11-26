import LeanVerification.PositiveDCompletion.SourceCoefficientExpansion
import LeanVerification.PositiveDCompletion.PhiSourceCoefficient0
import LeanVerification.PositiveDCompletion.PhiSourceCoefficient1
import LeanVerification.PositiveDCompletion.PhiSourceCoefficient2
import LeanVerification.PositiveDCompletion.PhiSourceCoefficient3
import LeanVerification.PositiveDCompletion.PhiSourceCoefficient4
import LeanVerification.PositiveDCompletion.RxSourceCoefficient0
import LeanVerification.PositiveDCompletion.RxSourceCoefficient1
import LeanVerification.PositiveDCompletion.RxSourceCoefficient2
import LeanVerification.PositiveDCompletion.RxSourceCoefficient3
import LeanVerification.PositiveDCompletion.RxSourceCoefficient4
import LeanVerification.PositiveDCompletion.RxSourceCoefficient5
import LeanVerification.PositiveDCompletion.RxSourceCoefficient6

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

theorem phi_numerator_identity (a f rho w : ℝ) :
    phiNumerator a f rho w=(1+a)*sourceT a f rho w := by
  rw [sourceT_coefficients]
  unfold phiNumerator
  rw [phi_source_coefficient_0,phi_source_coefficient_1,phi_source_coefficient_2,phi_source_coefficient_3,phi_source_coefficient_4]
  ring

theorem rx_numerator_identity (a f rho w : ℝ) :
    sourceH a f rho*rxNumerator a f rho w=(1+a)*sourceRXCleared a f rho w := by
  calc
    _=(((sourceH a f rho*rxNumCoeff0 a f rho)*w^0+((sourceH a f rho*rxNumCoeff1 a f rho)*w^1+(sourceH a f rho*rxNumCoeff2 a f rho)*w^2))+(((sourceH a f rho*rxNumCoeff3 a f rho)*w^3+(sourceH a f rho*rxNumCoeff4 a f rho)*w^4)+((sourceH a f rho*rxNumCoeff5 a f rho)*w^5+(sourceH a f rho*rxNumCoeff6 a f rho)*w^6))) := by
      unfold rxNumerator
      ring
    _=_ := by
      rw [rx_source_coefficient_0,rx_source_coefficient_1,rx_source_coefficient_2,rx_source_coefficient_3,rx_source_coefficient_4,rx_source_coefficient_5,rx_source_coefficient_6,sourceRXCleared_coefficients]
      ring

theorem source_F_fraction (m B j g A Z N T : ℝ)
    (hB : B≠0) (hj : j≠0) (hg : g≠0) (hA : A≠0) (hZ : Z≠0) (hN : N≠0) :
    (m*B/(4*A)*(T/(B*j^3*g^3)))/(Z*(N/(g*j))^3)=m*T/(4*Z*A*N^3) := by
  field_simp (disch := simp [hB,hj,hg,hA,hZ,hN]) [hB,hj,hg,hA,hZ,hN]
  ring

namespace SignedRegular
variable {a f rho w : ℝ} (h : SignedRegular a f rho)
include h

theorem modelF_eq_phiNumerator (hw : 1+w≠0) (hn : transportN a f rho w≠0) :
    modelF a f rho w=phiNumerator a f rho w/
      (4*(1+w)*modelA a f rho*(transportN a f rho w)^3) := by
  have hf0 : modelFZero a f rho=(1+a)*sourceB a f rho/(4*modelA a f rho) := by
    unfold modelFZero sourceB
    ring
  rw [modelF,hf0,h.modelPsi_eq_source,h.modelL_transportN,phi_numerator_identity]
  exact source_F_fraction (1+a) (sourceB a f rho) (1+f) (modelG a rho)
    (modelA a f rho) (1+w) (transportN a f rho w) (sourceT a f rho w)
    h.sourceB_ne h.j_ne h.g_ne h.A_ne hw hn


theorem modelRX_eq_rxNumerator (hw : 1+w≠0) (hn : transportN a f rho w≠0)
    (hPsi : modelPsi a f rho w≠0) :
    modelF a f rho w*modelR a f rho w=rxNumerator a f rho w/
      (4*a*(1+f)*(1+w)*modelA a f rho*(transportN a f rho w)^5) := by
  rw [h.modelRX_eq_source hw hn hPsi,←rx_numerator_identity]
  have hH := h.sourceH_ne
  rw [show 4*a*sourceH a f rho*(1+f)*(1+w)*modelA a f rho*(transportN a f rho w)^5=
    sourceH a f rho*(4*a*(1+f)*(1+w)*modelA a f rho*(transportN a f rho w)^5) by ring]
  exact mul_div_mul_left _ _ hH

end SignedRegular
end LeanVerification.PositiveDCompletion
