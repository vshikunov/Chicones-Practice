import LeanVerification.PositiveDCompletion.PoleRhoExpansion
import LeanVerification.PositiveDCompletion.RxPoleRho5Coefficient00
import LeanVerification.PositiveDCompletion.RxPoleRho5Coefficient01
import LeanVerification.PositiveDCompletion.RxPoleRho5Coefficient02
import LeanVerification.PositiveDCompletion.RxPoleRho5Coefficient03
import LeanVerification.PositiveDCompletion.RxPoleRho5Coefficient04
import LeanVerification.PositiveDCompletion.RxPoleRho5Coefficient05
import LeanVerification.PositiveDCompletion.RxPoleRho5Coefficient06
import LeanVerification.PositiveDCompletion.RxPoleRho5Coefficient07

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 64000000
set_option maxRecDepth 60000

theorem rx_pole_coefficient_5 (a f rho : ℝ) :
    rxPoleCoeff5 a f rho=((1 : ℝ)*(-1 : ℝ)^(5 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(1 : ℕ)*rxNumCoeff5 a f rho+(6 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(1 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho) := by
  have hl : rxPoleCoeff5 a f rho=poleRhoNode166 a f rho := by
    simp only [rxPoleCoeff5,poleRhoVariable,poleRhoUpper5,poleRhoNode021,poleRhoNode022,poleRhoInvariant5,poleRhoNode165,poleRhoNode166]
    ring
  have hr : poleRhoNode173 a f rho=((1 : ℝ)*(-1 : ℝ)^(5 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(1 : ℕ)*rxNumCoeff5 a f rho+(6 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(1 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho) := by
    simp only [poleRhoOne,poleRhoBase,poleRhoC,poleRhoRaw5,poleRhoRaw6,poleRhoNode063,poleRhoNode068,poleRhoScalar55,poleRhoNode168,poleRhoNode169,poleRhoScalar56,poleRhoNode171,poleRhoNode172,poleRhoNode173]
    ring
  rw [hl,←hr,poleRhoNode166_eval,poleRhoNode173_eval]
  rw [rx_pole_rho_5_0,rx_pole_rho_5_1,rx_pole_rho_5_2,rx_pole_rho_5_3,rx_pole_rho_5_4,rx_pole_rho_5_5,rx_pole_rho_5_6,rx_pole_rho_5_7]

end LeanVerification.PositiveDCompletion
