import LeanVerification.PositiveDCompletion.PoleCoefficientData

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 64000000
set_option maxRecDepth 60000

theorem pole_comparison_reduced_3 (a f rho : ℝ) :
    poleComparisonLeft3 a f rho+poleComparisonRight3 a f rho=poleComparisonTarget3 a f rho := by
  simp only [poleComparisonLeft3,poleComparisonRight3,poleComparisonTarget3,upperNum00,upperNum01,upperNum02,upperNum03,upperNum04,upperNum05,upperNum06,upperNum07,upperNum08,upperNum09,upperNum03Coeff0,upperNum03Coeff1,upperNum03Coeff2,upperNum03Coeff3,upperNum03Coeff4,upperNum04Coeff0,upperNum04Coeff1,upperNum04Coeff2,upperNum04Coeff3,upperNum04Coeff4,upperNum05Coeff0,upperNum05Coeff1,upperNum05Coeff2,upperNum05Coeff3,upperNum05Coeff4,upperNum06Coeff0,upperNum06Coeff1,upperNum06Coeff2,upperNum06Coeff3,upperNum06Coeff4,upperNum06Coeff5,upperNum06Coeff6,upperNum07Coeff0,upperNum07Coeff1,upperNum07Coeff2,upperNum07Coeff3,upperNum07Coeff4,upperNum07Coeff5,upperNum07Coeff6,upperNum08Coeff0,upperNum08Coeff1,upperNum08Coeff2,upperNum08Coeff3,upperNum08Coeff4,upperNum08Coeff5,upperNum08Coeff6,upperNum09Coeff0,upperNum09Coeff1,upperNum09Coeff2,upperNum09Coeff3,upperNum09Coeff4,upperNum09Coeff5,upperNum09Coeff6,poleCore00,poleCore01,poleCore02,poleCore03,poleCore04]
  ring

theorem pole_comparison_identity_3 (a f rho : ℝ) :
    -phiPoleCoeff4 a f rho*rxPoleCoeff5 a f rho+rxPoleCoeff6 a f rho*phiPoleCoeff3 a f rho=poleComparison3 a f rho := by
  have ha : -phiPoleCoeff4 a f rho*rxPoleCoeff5 a f rho=poleComparisonCommon3 a f rho*poleComparisonLeft3 a f rho := by
    unfold phiPoleCoeff4 rxPoleCoeff5 poleComparisonCommon3 poleComparisonLeft3
    ring
  have hb : rxPoleCoeff6 a f rho*phiPoleCoeff3 a f rho=poleComparisonCommon3 a f rho*poleComparisonRight3 a f rho := by
    unfold rxPoleCoeff6 phiPoleCoeff3 poleComparisonCommon3 poleComparisonRight3
    ring
  have hc : poleComparisonCommon3 a f rho*poleComparisonTarget3 a f rho=poleComparison3 a f rho := by
    unfold poleComparisonCommon3 poleComparisonTarget3 poleComparison3
    ring
  rw [ha,hb,←mul_add,pole_comparison_reduced_3,hc]

end LeanVerification.PositiveDCompletion
