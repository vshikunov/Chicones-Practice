import LeanVerification.PositiveDCompletion.PoleRhoExpansion
import LeanVerification.PositiveDCompletion.RxPoleRho3Coefficient00
import LeanVerification.PositiveDCompletion.RxPoleRho3Coefficient01
import LeanVerification.PositiveDCompletion.RxPoleRho3Coefficient02
import LeanVerification.PositiveDCompletion.RxPoleRho3Coefficient03
import LeanVerification.PositiveDCompletion.RxPoleRho3Coefficient04
import LeanVerification.PositiveDCompletion.RxPoleRho3Coefficient05
import LeanVerification.PositiveDCompletion.RxPoleRho3Coefficient06
import LeanVerification.PositiveDCompletion.RxPoleRho3Coefficient07
import LeanVerification.PositiveDCompletion.RxPoleRho3Coefficient08
import LeanVerification.PositiveDCompletion.RxPoleRho3Coefficient09

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 64000000
set_option maxRecDepth 60000

theorem rx_pole_coefficient_3 (a f rho : ℝ) :
    rxPoleCoeff3 a f rho=(((1 : ℝ)*(-1 : ℝ)^(3 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(3 : ℕ)*rxNumCoeff3 a f rho+(4 : ℝ)*(-1 : ℝ)^(4 : ℕ)*(sourceBase a f rho)^(1 : ℕ)*(sourceC a f rho)^(2 : ℕ)*rxNumCoeff4 a f rho)+((10 : ℝ)*(-1 : ℝ)^(5 : ℕ)*(sourceBase a f rho)^(2 : ℕ)*(sourceC a f rho)^(1 : ℕ)*rxNumCoeff5 a f rho+(20 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(3 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho)) := by
  have hl : rxPoleCoeff3 a f rho=poleRhoNode133 a f rho := by
    simp only [rxPoleCoeff3,poleRhoVariable,poleRhoG,poleRhoS,poleRhoUpper3,poleRhoNode021,poleRhoNode022,poleRhoInvariant3,poleRhoNode130,poleRhoNode131,poleRhoNode132,poleRhoNode133]
    ring
  have hr : poleRhoNode148 a f rho=(((1 : ℝ)*(-1 : ℝ)^(3 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(3 : ℕ)*rxNumCoeff3 a f rho+(4 : ℝ)*(-1 : ℝ)^(4 : ℕ)*(sourceBase a f rho)^(1 : ℕ)*(sourceC a f rho)^(2 : ℕ)*rxNumCoeff4 a f rho)+((10 : ℝ)*(-1 : ℝ)^(5 : ℕ)*(sourceBase a f rho)^(2 : ℕ)*(sourceC a f rho)^(1 : ℕ)*rxNumCoeff5 a f rho+(20 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(3 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho)) := by
    simp only [poleRhoOne,poleRhoBase,poleRhoC,poleRhoRaw3,poleRhoRaw4,poleRhoRaw5,poleRhoRaw6,poleRhoNode033,poleRhoNode034,poleRhoNode046,poleRhoNode051,poleRhoNode053,poleRhoNode058,poleRhoNode063,poleRhoNode068,poleRhoScalar33,poleRhoNode135,poleRhoNode136,poleRhoScalar34,poleRhoNode138,poleRhoNode139,poleRhoScalar35,poleRhoNode141,poleRhoNode142,poleRhoScalar36,poleRhoNode144,poleRhoNode145,poleRhoNode146,poleRhoNode147,poleRhoNode148]
    ring
  rw [hl,←hr,poleRhoNode133_eval,poleRhoNode148_eval]
  rw [rx_pole_rho_3_0,rx_pole_rho_3_1,rx_pole_rho_3_2,rx_pole_rho_3_3,rx_pole_rho_3_4,rx_pole_rho_3_5,rx_pole_rho_3_6,rx_pole_rho_3_7,rx_pole_rho_3_8,rx_pole_rho_3_9]

end LeanVerification.PositiveDCompletion
