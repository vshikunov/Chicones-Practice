import LeanVerification.PositiveDCompletion.PoleCoefficientData

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 64000000
set_option maxRecDepth 60000

theorem pole_comparison_reduced_0 (a f rho : ℝ) :
    poleComparisonLeft0 a f rho+poleComparisonRight0 a f rho=poleComparisonTarget0 a f rho := by
  simp only [poleComparisonLeft0,poleComparisonRight0,poleComparisonTarget0,upperNum00,upperNum01,upperNum02,upperNum03,upperNum04,upperNum05,upperNum06,upperNum07,upperNum08,upperNum09,upperNum03Coeff0,upperNum03Coeff1,upperNum03Coeff2,upperNum03Coeff3,upperNum03Coeff4,upperNum04Coeff0,upperNum04Coeff1,upperNum04Coeff2,upperNum04Coeff3,upperNum04Coeff4,upperNum05Coeff0,upperNum05Coeff1,upperNum05Coeff2,upperNum05Coeff3,upperNum05Coeff4,upperNum06Coeff0,upperNum06Coeff1,upperNum06Coeff2,upperNum06Coeff3,upperNum06Coeff4,upperNum06Coeff5,upperNum06Coeff6,upperNum07Coeff0,upperNum07Coeff1,upperNum07Coeff2,upperNum07Coeff3,upperNum07Coeff4,upperNum07Coeff5,upperNum07Coeff6,upperNum08Coeff0,upperNum08Coeff1,upperNum08Coeff2,upperNum08Coeff3,upperNum08Coeff4,upperNum08Coeff5,upperNum08Coeff6,upperNum09Coeff0,upperNum09Coeff1,upperNum09Coeff2,upperNum09Coeff3,upperNum09Coeff4,upperNum09Coeff5,upperNum09Coeff6,poleCore00,poleCore01,poleCore02,poleCore03,poleCore04]
  ring

theorem pole_comparison_identity_0 (a f rho : ℝ) :
    -phiPoleCoeff4 a f rho*rxPoleCoeff2 a f rho+rxPoleCoeff6 a f rho*phiPoleCoeff0 a f rho=poleComparison0 a f rho := by
  have ha : -phiPoleCoeff4 a f rho*rxPoleCoeff2 a f rho=poleComparisonCommon0 a f rho*poleComparisonLeft0 a f rho := by
    unfold phiPoleCoeff4 rxPoleCoeff2 poleComparisonCommon0 poleComparisonLeft0
    ring
  have hb : rxPoleCoeff6 a f rho*phiPoleCoeff0 a f rho=poleComparisonCommon0 a f rho*poleComparisonRight0 a f rho := by
    unfold rxPoleCoeff6 phiPoleCoeff0 poleComparisonCommon0 poleComparisonRight0
    ring
  have hc : poleComparisonCommon0 a f rho*poleComparisonTarget0 a f rho=poleComparison0 a f rho := by
    unfold poleComparisonCommon0 poleComparisonTarget0 poleComparison0
    ring
  rw [ha,hb,←mul_add,pole_comparison_reduced_0,hc]

end LeanVerification.PositiveDCompletion
