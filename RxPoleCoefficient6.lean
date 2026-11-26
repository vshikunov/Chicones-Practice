import LeanVerification.PositiveDCompletion.PoleRhoExpansion
import LeanVerification.PositiveDCompletion.RxPoleRho6Coefficient00
import LeanVerification.PositiveDCompletion.RxPoleRho6Coefficient01
import LeanVerification.PositiveDCompletion.RxPoleRho6Coefficient02
import LeanVerification.PositiveDCompletion.RxPoleRho6Coefficient03
import LeanVerification.PositiveDCompletion.RxPoleRho6Coefficient04
import LeanVerification.PositiveDCompletion.RxPoleRho6Coefficient05
import LeanVerification.PositiveDCompletion.RxPoleRho6Coefficient06

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 64000000
set_option maxRecDepth 60000

theorem rx_pole_coefficient_6 (a f rho : ℝ) :
    rxPoleCoeff6 a f rho=(1 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho := by
  have hl : rxPoleCoeff6 a f rho=poleRhoNode176 a f rho := by
    simp only [rxPoleCoeff6,poleRhoVariable,poleRhoCore4,poleRhoNode021,poleRhoNode022,poleRhoInvariant6,poleRhoNode175,poleRhoNode176]
    ring
  have hr : poleRhoNode179 a f rho=(1 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho := by
    simp only [poleRhoOne,poleRhoRaw6,poleRhoNode068,poleRhoScalar66,poleRhoNode178,poleRhoNode179]
    ring
  rw [hl,←hr,poleRhoNode176_eval,poleRhoNode179_eval]
  rw [rx_pole_rho_6_0,rx_pole_rho_6_1,rx_pole_rho_6_2,rx_pole_rho_6_3,rx_pole_rho_6_4,rx_pole_rho_6_5,rx_pole_rho_6_6]

end LeanVerification.PositiveDCompletion
