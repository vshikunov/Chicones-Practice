import LeanVerification.PositiveDCompletion.PoleCoefficientData

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 64000000
set_option maxRecDepth 60000

theorem phi_pole_coefficient_3 (a f rho : ℝ) :
    phiPoleCoeff3 a f rho=((1 : ℝ)*(-1 : ℝ)^(3 : ℕ)*(sourceBase a f rho)^(0 : ℕ)*(sourceC a f rho)^(1 : ℕ)*phiNumCoeff3 a f rho+(4 : ℝ)*(-1 : ℝ)^(4 : ℕ)*(sourceBase a f rho)^(1 : ℕ)*(sourceC a f rho)^(0 : ℕ)*phiNumCoeff4 a f rho) := by
  simp only [phiPoleCoeff3,phiNumCoeff3,phiNumCoeff4,upperNum00,upperNum01,upperNum02,upperNum03,upperNum04,upperNum05,upperNum06,upperNum07,upperNum08,upperNum09,upperNum03Coeff0,upperNum03Coeff1,upperNum03Coeff2,upperNum03Coeff3,upperNum03Coeff4,upperNum04Coeff0,upperNum04Coeff1,upperNum04Coeff2,upperNum04Coeff3,upperNum04Coeff4,upperNum05Coeff0,upperNum05Coeff1,upperNum05Coeff2,upperNum05Coeff3,upperNum05Coeff4,upperNum06Coeff0,upperNum06Coeff1,upperNum06Coeff2,upperNum06Coeff3,upperNum06Coeff4,upperNum06Coeff5,upperNum06Coeff6,upperNum07Coeff0,upperNum07Coeff1,upperNum07Coeff2,upperNum07Coeff3,upperNum07Coeff4,upperNum07Coeff5,upperNum07Coeff6,upperNum08Coeff0,upperNum08Coeff1,upperNum08Coeff2,upperNum08Coeff3,upperNum08Coeff4,upperNum08Coeff5,upperNum08Coeff6,upperNum09Coeff0,upperNum09Coeff1,upperNum09Coeff2,upperNum09Coeff3,upperNum09Coeff4,upperNum09Coeff5,upperNum09Coeff6,poleCore00,poleCore01,poleCore02,poleCore03,poleCore04,sourceBase,sourceC,modelG]
  ring

end LeanVerification.PositiveDCompletion
