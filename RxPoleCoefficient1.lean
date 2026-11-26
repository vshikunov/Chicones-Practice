import LeanVerification.PositiveDCompletion.PoleRhoExpansion
import LeanVerification.PositiveDCompletion.RxPoleRho1Coefficient00
import LeanVerification.PositiveDCompletion.RxPoleRho1Coefficient01
import LeanVerification.PositiveDCompletion.RxPoleRho1Coefficient02
import LeanVerification.PositiveDCompletion.RxPoleRho1Coefficient03
import LeanVerification.PositiveDCompletion.RxPoleRho1Coefficient04
import LeanVerification.PositiveDCompletion.RxPoleRho1Coefficient05
import LeanVerification.PositiveDCompletion.RxPoleRho1Coefficient06
import LeanVerification.PositiveDCompletion.RxPoleRho1Coefficient07
import LeanVerification.PositiveDCompletion.RxPoleRho1Coefficient08
import LeanVerification.PositiveDCompletion.RxPoleRho1Coefficient09
import LeanVerification.PositiveDCompletion.RxPoleRho1Coefficient10
import LeanVerification.PositiveDCompletion.RxPoleRho1Coefficient11

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 64000000
set_option maxRecDepth 60000

theorem rx_pole_coefficient_1 (a f rho : ℝ) :
    rxPoleCoeff1 a f rho=(((1 : ℝ)*(-1 : ℝ)^(1 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(5 : ℕ)*rxNumCoeff1 a f rho+((2 : ℝ)*(-1 : ℝ)^(2 : ℕ)*(sourceBase a f rho)^(1 : ℕ)*(sourceC a f rho)^(4 : ℕ)*rxNumCoeff2 a f rho+(3 : ℝ)*(-1 : ℝ)^(3 : ℕ)*(sourceBase a f rho)^(2 : ℕ)*(sourceC a f rho)^(3 : ℕ)*rxNumCoeff3 a f rho))+((4 : ℝ)*(-1 : ℝ)^(4 : ℕ)*(sourceBase a f rho)^(3 : ℕ)*(sourceC a f rho)^(2 : ℕ)*rxNumCoeff4 a f rho+((5 : ℝ)*(-1 : ℝ)^(5 : ℕ)*(sourceBase a f rho)^(4 : ℕ)*(sourceC a f rho)^(1 : ℕ)*rxNumCoeff5 a f rho+(6 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(5 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho))) := by
  have hl : rxPoleCoeff1 a f rho=poleRhoNode081 a f rho := by
    simp only [rxPoleCoeff1,poleRhoVariable,poleRhoG,poleRhoS,poleRhoUpper1,poleRhoNode021,poleRhoNode022,poleRhoNode023,poleRhoNode025,poleRhoInvariant1,poleRhoNode077,poleRhoNode078,poleRhoNode079,poleRhoNode080,poleRhoNode081]
    ring
  have hr : poleRhoNode104 a f rho=(((1 : ℝ)*(-1 : ℝ)^(1 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(5 : ℕ)*rxNumCoeff1 a f rho+((2 : ℝ)*(-1 : ℝ)^(2 : ℕ)*(sourceBase a f rho)^(1 : ℕ)*(sourceC a f rho)^(4 : ℕ)*rxNumCoeff2 a f rho+(3 : ℝ)*(-1 : ℝ)^(3 : ℕ)*(sourceBase a f rho)^(2 : ℕ)*(sourceC a f rho)^(3 : ℕ)*rxNumCoeff3 a f rho))+((4 : ℝ)*(-1 : ℝ)^(4 : ℕ)*(sourceBase a f rho)^(3 : ℕ)*(sourceC a f rho)^(2 : ℕ)*rxNumCoeff4 a f rho+((5 : ℝ)*(-1 : ℝ)^(5 : ℕ)*(sourceBase a f rho)^(4 : ℕ)*(sourceC a f rho)^(1 : ℕ)*rxNumCoeff5 a f rho+(6 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(5 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho))) := by
    simp only [poleRhoOne,poleRhoBase,poleRhoC,poleRhoRaw1,poleRhoRaw2,poleRhoRaw3,poleRhoRaw4,poleRhoRaw5,poleRhoRaw6,poleRhoNode033,poleRhoNode034,poleRhoNode040,poleRhoNode041,poleRhoNode043,poleRhoNode046,poleRhoNode048,poleRhoNode051,poleRhoNode053,poleRhoNode056,poleRhoNode058,poleRhoNode061,poleRhoNode063,poleRhoNode068,poleRhoScalar11,poleRhoNode083,poleRhoNode084,poleRhoScalar12,poleRhoNode086,poleRhoNode087,poleRhoScalar13,poleRhoNode089,poleRhoNode090,poleRhoScalar14,poleRhoNode092,poleRhoNode093,poleRhoScalar15,poleRhoNode095,poleRhoNode096,poleRhoScalar16,poleRhoNode098,poleRhoNode099,poleRhoNode100,poleRhoNode101,poleRhoNode102,poleRhoNode103,poleRhoNode104]
    ring
  rw [hl,←hr,poleRhoNode081_eval,poleRhoNode104_eval]
  rw [rx_pole_rho_1_0,rx_pole_rho_1_1,rx_pole_rho_1_2,rx_pole_rho_1_3,rx_pole_rho_1_4,rx_pole_rho_1_5,rx_pole_rho_1_6,rx_pole_rho_1_7,rx_pole_rho_1_8,rx_pole_rho_1_9,rx_pole_rho_1_10,rx_pole_rho_1_11]

end LeanVerification.PositiveDCompletion
