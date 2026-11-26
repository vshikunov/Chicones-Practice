import LeanVerification.PositiveDCompletion.SourceCoefficientData

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 48000000
set_option maxRecDepth 50000

theorem sourceT_coefficients (a f rho w : ℝ) :
    sourceT a f rho w=(((sourceTCoeff0 a f rho)*w^(0 : ℕ)+(sourceTCoeff1 a f rho)*w^(1 : ℕ))+((sourceTCoeff2 a f rho)*w^(2 : ℕ)+((sourceTCoeff3 a f rho)*w^(3 : ℕ)+(sourceTCoeff4 a f rho)*w^(4 : ℕ)))) := by
  exact source_t_coeff_assembly (sourceB a f rho) (1+f) (modelG a rho)
    (weakNum00 a f rho) (weakNum01 a f rho) (weakNum02 a f rho) (weakNum03 a f rho) w

theorem sourceV_coefficients (a f rho w : ℝ) :
    sourceV a f rho w=(((sourceVCoeff0 a f rho)*w^(0 : ℕ)+((sourceVCoeff1 a f rho)*w^(1 : ℕ)+(sourceVCoeff2 a f rho)*w^(2 : ℕ)))+((sourceVCoeff3 a f rho)*w^(3 : ℕ)+((sourceVCoeff4 a f rho)*w^(4 : ℕ)+(sourceVCoeff5 a f rho)*w^(5 : ℕ)))) := by
  exact source_v_coeff_assembly a (sourceB a f rho) (1+f) (modelG a rho)
    (sourceH a f rho) (sourceM a f rho)
    (weakNum00 a f rho) (weakNum01 a f rho) (weakNum02 a f rho) (weakNum03 a f rho) (weakNum04 a f rho) (weakNum05 a f rho) (weakNum06 a f rho) (weakNum07 a f rho) (weakNum08 a f rho) w

theorem sourcePole_coefficients (a f rho w : ℝ) :
    sourcePole a f rho w=sourcePoleCoeff1 a f rho*w+sourcePoleCoeff2 a f rho*w^(2 : ℕ) := by rfl

theorem transportN_source (a f rho w : ℝ) :
    transportN a f rho w=sourceBase a f rho+sourceC a f rho*w := by rfl

theorem sourceRXCleared_coefficients (a f rho w : ℝ) :
    sourceRXCleared a f rho w=(((sourceRXCoeff0 a f rho)*w^(0 : ℕ)+((sourceRXCoeff1 a f rho)*w^(1 : ℕ)+(sourceRXCoeff2 a f rho)*w^(2 : ℕ)))+(((sourceRXCoeff3 a f rho)*w^(3 : ℕ)+(sourceRXCoeff4 a f rho)*w^(4 : ℕ))+((sourceRXCoeff5 a f rho)*w^(5 : ℕ)+(sourceRXCoeff6 a f rho)*w^(6 : ℕ)))) := by
  unfold sourceRXCleared
  rw [sourceT_coefficients,sourceV_coefficients,sourcePole_coefficients,transportN_source]
  exact source_coeff_assembly a f (sourceH a f rho) (sourceBase a f rho) (sourceC a f rho) (sourceRZero a f rho) (sourcePoleCoeff1 a f rho) (sourcePoleCoeff2 a f rho) w
    (sourceTCoeff0 a f rho) (sourceTCoeff1 a f rho) (sourceTCoeff2 a f rho) (sourceTCoeff3 a f rho) (sourceTCoeff4 a f rho)
    (sourceVCoeff0 a f rho) (sourceVCoeff1 a f rho) (sourceVCoeff2 a f rho) (sourceVCoeff3 a f rho) (sourceVCoeff4 a f rho) (sourceVCoeff5 a f rho)

end LeanVerification.PositiveDCompletion
