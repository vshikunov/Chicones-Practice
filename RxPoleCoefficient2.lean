import LeanVerification.PositiveDCompletion.PoleRhoExpansion
import LeanVerification.PositiveDCompletion.RxPoleRho2Coefficient00
import LeanVerification.PositiveDCompletion.RxPoleRho2Coefficient01
import LeanVerification.PositiveDCompletion.RxPoleRho2Coefficient02
import LeanVerification.PositiveDCompletion.RxPoleRho2Coefficient03
import LeanVerification.PositiveDCompletion.RxPoleRho2Coefficient04
import LeanVerification.PositiveDCompletion.RxPoleRho2Coefficient05
import LeanVerification.PositiveDCompletion.RxPoleRho2Coefficient06
import LeanVerification.PositiveDCompletion.RxPoleRho2Coefficient07
import LeanVerification.PositiveDCompletion.RxPoleRho2Coefficient08
import LeanVerification.PositiveDCompletion.RxPoleRho2Coefficient09
import LeanVerification.PositiveDCompletion.RxPoleRho2Coefficient10

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 64000000
set_option maxRecDepth 60000

theorem rx_pole_coefficient_2 (a f rho : ℝ) :
    rxPoleCoeff2 a f rho=(((1 : ℝ)*(-1 : ℝ)^(2 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(4 : ℕ)*rxNumCoeff2 a f rho+(3 : ℝ)*(-1 : ℝ)^(3 : ℕ)*(sourceBase a f rho)^(1 : ℕ)*(sourceC a f rho)^(3 : ℕ)*rxNumCoeff3 a f rho)+((6 : ℝ)*(-1 : ℝ)^(4 : ℕ)*(sourceBase a f rho)^(2 : ℕ)*(sourceC a f rho)^(2 : ℕ)*rxNumCoeff4 a f rho+((10 : ℝ)*(-1 : ℝ)^(5 : ℕ)*(sourceBase a f rho)^(3 : ℕ)*(sourceC a f rho)^(1 : ℕ)*rxNumCoeff5 a f rho+(15 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(4 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho))) := by
  have hl : rxPoleCoeff2 a f rho=poleRhoNode109 a f rho := by
    simp only [rxPoleCoeff2,poleRhoVariable,poleRhoG,poleRhoS,poleRhoUpper2,poleRhoNode021,poleRhoNode022,poleRhoNode025,poleRhoInvariant2,poleRhoNode106,poleRhoNode107,poleRhoNode108,poleRhoNode109]
    ring
  have hr : poleRhoNode128 a f rho=(((1 : ℝ)*(-1 : ℝ)^(2 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(4 : ℕ)*rxNumCoeff2 a f rho+(3 : ℝ)*(-1 : ℝ)^(3 : ℕ)*(sourceBase a f rho)^(1 : ℕ)*(sourceC a f rho)^(3 : ℕ)*rxNumCoeff3 a f rho)+((6 : ℝ)*(-1 : ℝ)^(4 : ℕ)*(sourceBase a f rho)^(2 : ℕ)*(sourceC a f rho)^(2 : ℕ)*rxNumCoeff4 a f rho+((10 : ℝ)*(-1 : ℝ)^(5 : ℕ)*(sourceBase a f rho)^(3 : ℕ)*(sourceC a f rho)^(1 : ℕ)*rxNumCoeff5 a f rho+(15 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(4 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho))) := by
    simp only [poleRhoOne,poleRhoBase,poleRhoC,poleRhoRaw2,poleRhoRaw3,poleRhoRaw4,poleRhoRaw5,poleRhoRaw6,poleRhoNode033,poleRhoNode034,poleRhoNode040,poleRhoNode046,poleRhoNode048,poleRhoNode051,poleRhoNode053,poleRhoNode056,poleRhoNode058,poleRhoNode063,poleRhoNode068,poleRhoScalar22,poleRhoNode111,poleRhoNode112,poleRhoScalar23,poleRhoNode114,poleRhoNode115,poleRhoScalar24,poleRhoNode117,poleRhoNode118,poleRhoScalar25,poleRhoNode120,poleRhoNode121,poleRhoScalar26,poleRhoNode123,poleRhoNode124,poleRhoNode125,poleRhoNode126,poleRhoNode127,poleRhoNode128]
    ring
  rw [hl,←hr,poleRhoNode109_eval,poleRhoNode128_eval]
  rw [rx_pole_rho_2_0,rx_pole_rho_2_1,rx_pole_rho_2_2,rx_pole_rho_2_3,rx_pole_rho_2_4,rx_pole_rho_2_5,rx_pole_rho_2_6,rx_pole_rho_2_7,rx_pole_rho_2_8,rx_pole_rho_2_9,rx_pole_rho_2_10]

end LeanVerification.PositiveDCompletion
