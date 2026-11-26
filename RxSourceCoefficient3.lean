import LeanVerification.PositiveDCompletion.SourceCoefficientData

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 48000000
set_option maxRecDepth 50000

theorem rx_source_coefficient_3 (a f rho : ℝ) :
    sourceH a f rho*rxNumCoeff3 a f rho=(1+a)*sourceRXCoeff3 a f rho := by
  simp only [rxNumCoeff3,sourceRXCoeff3,sourceB,sourceH,sourceM,sourceC,sourceFlow,sourceBase,sourceRZero,modelG,sourceTCoeff0,sourceTCoeff1,sourceTCoeff2,sourceTCoeff3,sourceTCoeff4,sourcePoleCoeff1,sourcePoleCoeff2,sourceVCoeff0,sourceVCoeff1,sourceVCoeff2,sourceVCoeff3,sourceVCoeff4,sourceVCoeff5,weakNum00,weakNum01,weakNum02,weakNum03,weakNum04,weakNum05,weakNum06,weakNum07,weakNum08,weakNum09]
  ring

end LeanVerification.PositiveDCompletion
