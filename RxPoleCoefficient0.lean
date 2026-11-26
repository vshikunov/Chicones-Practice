import LeanVerification.PositiveDCompletion.PoleRhoExpansion
import LeanVerification.PositiveDCompletion.RxPoleRho0Coefficient00
import LeanVerification.PositiveDCompletion.RxPoleRho0Coefficient01
import LeanVerification.PositiveDCompletion.RxPoleRho0Coefficient02
import LeanVerification.PositiveDCompletion.RxPoleRho0Coefficient03
import LeanVerification.PositiveDCompletion.RxPoleRho0Coefficient04
import LeanVerification.PositiveDCompletion.RxPoleRho0Coefficient05
import LeanVerification.PositiveDCompletion.RxPoleRho0Coefficient06
import LeanVerification.PositiveDCompletion.RxPoleRho0Coefficient07
import LeanVerification.PositiveDCompletion.RxPoleRho0Coefficient08
import LeanVerification.PositiveDCompletion.RxPoleRho0Coefficient09
import LeanVerification.PositiveDCompletion.RxPoleRho0Coefficient10
import LeanVerification.PositiveDCompletion.RxPoleRho0Coefficient11
import LeanVerification.PositiveDCompletion.RxPoleRho0Coefficient12

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 64000000
set_option maxRecDepth 60000

theorem rx_pole_coefficient_0 (a f rho : ℝ) :
    rxPoleCoeff0 a f rho=(((1 : ℝ)*(-1 : ℝ)^(0 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(6 : ℕ)*rxNumCoeff0 a f rho+((1 : ℝ)*(-1 : ℝ)^(1 : ℕ)*(sourceBase a f rho)^(1 : ℕ)*(sourceC a f rho)^(5 : ℕ)*rxNumCoeff1 a f rho+(1 : ℝ)*(-1 : ℝ)^(2 : ℕ)*(sourceBase a f rho)^(2 : ℕ)*(sourceC a f rho)^(4 : ℕ)*rxNumCoeff2 a f rho))+(((1 : ℝ)*(-1 : ℝ)^(3 : ℕ)*(sourceBase a f rho)^(3 : ℕ)*(sourceC a f rho)^(3 : ℕ)*rxNumCoeff3 a f rho+(1 : ℝ)*(-1 : ℝ)^(4 : ℕ)*(sourceBase a f rho)^(4 : ℕ)*(sourceC a f rho)^(2 : ℕ)*rxNumCoeff4 a f rho)+((1 : ℝ)*(-1 : ℝ)^(5 : ℕ)*(sourceBase a f rho)^(5 : ℕ)*(sourceC a f rho)^(1 : ℕ)*rxNumCoeff5 a f rho+(1 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(6 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho))) := by
  have hl : rxPoleCoeff0 a f rho=poleRhoNode031 a f rho := by
    simp only [rxPoleCoeff0,poleRhoVariable,poleRhoG,poleRhoS,poleRhoCore0,poleRhoInvariant0,poleRhoNode021,poleRhoNode022,poleRhoNode023,poleRhoNode024,poleRhoNode025,poleRhoNode026,poleRhoNode027,poleRhoNode028,poleRhoNode029,poleRhoNode030,poleRhoNode031]
    ring
  have hr : poleRhoNode075 a f rho=(((1 : ℝ)*(-1 : ℝ)^(0 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(6 : ℕ)*rxNumCoeff0 a f rho+((1 : ℝ)*(-1 : ℝ)^(1 : ℕ)*(sourceBase a f rho)^(1 : ℕ)*(sourceC a f rho)^(5 : ℕ)*rxNumCoeff1 a f rho+(1 : ℝ)*(-1 : ℝ)^(2 : ℕ)*(sourceBase a f rho)^(2 : ℕ)*(sourceC a f rho)^(4 : ℕ)*rxNumCoeff2 a f rho))+(((1 : ℝ)*(-1 : ℝ)^(3 : ℕ)*(sourceBase a f rho)^(3 : ℕ)*(sourceC a f rho)^(3 : ℕ)*rxNumCoeff3 a f rho+(1 : ℝ)*(-1 : ℝ)^(4 : ℕ)*(sourceBase a f rho)^(4 : ℕ)*(sourceC a f rho)^(2 : ℕ)*rxNumCoeff4 a f rho)+((1 : ℝ)*(-1 : ℝ)^(5 : ℕ)*(sourceBase a f rho)^(5 : ℕ)*(sourceC a f rho)^(1 : ℕ)*rxNumCoeff5 a f rho+(1 : ℝ)*(-1 : ℝ)^(6 : ℕ)*(sourceBase a f rho)^(6 : ℕ)*(sourceC a f rho)^(0 : ℕ)*rxNumCoeff6 a f rho))) := by
    simp only [poleRhoOne,poleRhoBase,poleRhoC,poleRhoRaw0,poleRhoRaw1,poleRhoRaw2,poleRhoRaw3,poleRhoRaw4,poleRhoRaw5,poleRhoRaw6,poleRhoScalar00,poleRhoNode033,poleRhoNode034,poleRhoNode035,poleRhoNode036,poleRhoNode037,poleRhoNode038,poleRhoScalar01,poleRhoNode040,poleRhoNode041,poleRhoNode042,poleRhoNode043,poleRhoNode044,poleRhoScalar02,poleRhoNode046,poleRhoNode047,poleRhoNode048,poleRhoNode049,poleRhoScalar03,poleRhoNode051,poleRhoNode052,poleRhoNode053,poleRhoNode054,poleRhoScalar04,poleRhoNode056,poleRhoNode057,poleRhoNode058,poleRhoNode059,poleRhoScalar05,poleRhoNode061,poleRhoNode062,poleRhoNode063,poleRhoNode064,poleRhoScalar06,poleRhoNode066,poleRhoNode067,poleRhoNode068,poleRhoNode069,poleRhoNode070,poleRhoNode071,poleRhoNode072,poleRhoNode073,poleRhoNode074,poleRhoNode075]
    ring
  rw [hl,←hr,poleRhoNode031_eval,poleRhoNode075_eval]
  rw [rx_pole_rho_0_0,rx_pole_rho_0_1,rx_pole_rho_0_2,rx_pole_rho_0_3,rx_pole_rho_0_4,rx_pole_rho_0_5,rx_pole_rho_0_6,rx_pole_rho_0_7,rx_pole_rho_0_8,rx_pole_rho_0_9,rx_pole_rho_0_10,rx_pole_rho_0_11,rx_pole_rho_0_12]

end LeanVerification.PositiveDCompletion
