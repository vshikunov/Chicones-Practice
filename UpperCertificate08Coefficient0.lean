import LeanVerification.PositiveDCompletion.UpperCertificate08Coefficient0Kernel
import LeanVerification.PositiveDCompletion.UpperCertificate08Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperAtom08Coeff0_identity (a t : ℝ) :
    upperAtom08Coeff0 a t=(((((upperCertificate08Weight00 a)*(upperCertificate08Block00Coeff0 t)+((upperCertificate08Weight01 a)*(upperCertificate08Block01Coeff0 t)+(upperCertificate08Weight02 a)*(upperCertificate08Block02Coeff0 t)))+((upperCertificate08Weight03 a)*(upperCertificate08Block03Coeff0 t)+((upperCertificate08Weight04 a)*(upperCertificate08Block04Coeff0 t)+(upperCertificate08Weight05 a)*(upperCertificate08Block05Coeff0 t))))+(((upperCertificate08Weight06 a)*(upperCertificate08Block06Coeff0 t)+((upperCertificate08Weight07 a)*(upperCertificate08Block07Coeff0 t)+(upperCertificate08Weight08 a)*(upperCertificate08Block08Coeff0 t)))+(((upperCertificate08Weight09 a)*(upperCertificate08Block09Coeff0 t)+(upperCertificate08Weight10 a)*(upperCertificate08Block10Coeff0 t))+((upperCertificate08Weight11 a)*(upperCertificate08Block11Coeff0 t)+(upperCertificate08Weight12 a)*(upperCertificate08Block12Coeff0 t)))))+((((upperCertificate08Weight13 a)*(upperCertificate08Block13Coeff0 t)+((upperCertificate08Weight14 a)*(upperCertificate08Block14Coeff0 t)+(upperCertificate08Weight15 a)*(upperCertificate08Block15Coeff0 t)))+(((upperCertificate08Weight16 a)*(upperCertificate08Block16Coeff0 t)+(upperCertificate08Weight17 a)*(upperCertificate08Block17Coeff0 t))+((upperCertificate08Weight18 a)*(upperCertificate08Block18Coeff0 t)+(upperCertificate08Weight19 a)*(upperCertificate08Block19Coeff0 t))))+(((upperCertificate08Weight20 a)*(upperCertificate08Block20Coeff0 t)+((upperCertificate08Weight21 a)*(upperCertificate08Block21Coeff0 t)+(upperCertificate08Weight22 a)*(upperCertificate08Block22Coeff0 t)))+(((upperCertificate08Weight23 a)*(upperCertificate08Block23Coeff0 t)+(upperCertificate08Weight24 a)*(upperCertificate08Block24Coeff0 t))+((upperCertificate08Weight25 a)*(upperCertificate08Block25Coeff0 t)+(upperCertificate08Weight26 a)*(upperCertificate08Block26Coeff0 t)))))) := by
  exact upperAtom08Coeff0_identity_source_value a t

end LeanVerification.PositiveDCompletion
