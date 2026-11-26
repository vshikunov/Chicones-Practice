import LeanVerification.PositiveDCompletion.PoleRhoExpansion
import LeanVerification.PositiveDCompletion.RxPoleRho4Coefficient00
import LeanVerification.PositiveDCompletion.RxPoleRho4Coefficient01
import LeanVerification.PositiveDCompletion.RxPoleRho4Coefficient02
import LeanVerification.PositiveDCompletion.RxPoleRho4Coefficient03
import LeanVerification.PositiveDCompletion.RxPoleRho4Coefficient04
import LeanVerification.PositiveDCompletion.RxPoleRho4Coefficient05
import LeanVerification.PositiveDCompletion.RxPoleRho4Coefficient06
import LeanVerification.PositiveDCompletion.RxPoleRho4Coefficient07
import LeanVerification.PositiveDCompletion.RxPoleRho4Coefficient08

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 64000000
set_option maxRecDepth 60000

theorem rx_pole_coefficient_4 (a f rho : ℝ) :
    rxPoleCoeff4 a f rho=((1 : ℝ)*(-1 : ℝ)^(4 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(2 : ℕ)*rxNumCoeff4 a f rho+((5 : ℝ)*(-1 : ℝ)^(5 : ℕ)*(sourceBase a f rho)^(1 : ℕ)*(sourceC a f rho)^(1 : ℕ)*rxNumCoeff5 a f rho+(15 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(2 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho)) := by
  have hl : rxPoleCoeff4 a f rho=poleRhoNode152 a f rho := by
    simp only [rxPoleCoeff4,poleRhoVariable,poleRhoG,poleRhoUpper4,poleRhoNode021,poleRhoNode022,poleRhoInvariant4,poleRhoNode150,poleRhoNode151,poleRhoNode152]
    ring
  have hr : poleRhoNode163 a f rho=((1 : ℝ)*(-1 : ℝ)^(4 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(2 : ℕ)*rxNumCoeff4 a f rho+((5 : ℝ)*(-1 : ℝ)^(5 : ℕ)*(sourceBase a f rho)^(1 : ℕ)*(sourceC a f rho)^(1 : ℕ)*rxNumCoeff5 a f rho+(15 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(2 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho)) := by
    simp only [poleRhoOne,poleRhoBase,poleRhoC,poleRhoRaw4,poleRhoRaw5,poleRhoRaw6,poleRhoNode033,poleRhoNode046,poleRhoNode058,poleRhoNode063,poleRhoNode068,poleRhoScalar44,poleRhoNode154,poleRhoNode155,poleRhoScalar45,poleRhoNode157,poleRhoNode158,poleRhoScalar46,poleRhoNode160,poleRhoNode161,poleRhoNode162,poleRhoNode163]
    ring
  rw [hl,←hr,poleRhoNode152_eval,poleRhoNode163_eval]
  rw [rx_pole_rho_4_0,rx_pole_rho_4_1,rx_pole_rho_4_2,rx_pole_rho_4_3,rx_pole_rho_4_4,rx_pole_rho_4_5,rx_pole_rho_4_6,rx_pole_rho_4_7,rx_pole_rho_4_8]

end LeanVerification.PositiveDCompletion
