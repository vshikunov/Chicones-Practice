import LeanVerification.PositiveDCompletion.UpperCertificate08Coefficient3Kernel
import LeanVerification.PositiveDCompletion.UpperCertificate08Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperAtom08Coeff3_identity (a t : ℝ) :
    upperAtom08Coeff3 a t=(((((upperCertificate08Weight00 a)*(upperCertificate08Block00Coeff3 t)+((upperCertificate08Weight01 a)*(upperCertificate08Block01Coeff3 t)+(upperCertificate08Weight02 a)*(upperCertificate08Block02Coeff3 t)))+((upperCertificate08Weight03 a)*(upperCertificate08Block03Coeff3 t)+((upperCertificate08Weight04 a)*(upperCertificate08Block04Coeff3 t)+(upperCertificate08Weight05 a)*(upperCertificate08Block05Coeff3 t))))+(((upperCertificate08Weight06 a)*(upperCertificate08Block06Coeff3 t)+((upperCertificate08Weight07 a)*(upperCertificate08Block07Coeff3 t)+(upperCertificate08Weight08 a)*(upperCertificate08Block08Coeff3 t)))+(((upperCertificate08Weight09 a)*(upperCertificate08Block09Coeff3 t)+(upperCertificate08Weight10 a)*(upperCertificate08Block10Coeff3 t))+((upperCertificate08Weight11 a)*(upperCertificate08Block11Coeff3 t)+(upperCertificate08Weight12 a)*(upperCertificate08Block12Coeff3 t)))))+((((upperCertificate08Weight13 a)*(upperCertificate08Block13Coeff3 t)+((upperCertificate08Weight14 a)*(upperCertificate08Block14Coeff3 t)+(upperCertificate08Weight15 a)*(upperCertificate08Block15Coeff3 t)))+(((upperCertificate08Weight16 a)*(upperCertificate08Block16Coeff3 t)+(upperCertificate08Weight17 a)*(upperCertificate08Block17Coeff3 t))+((upperCertificate08Weight18 a)*(upperCertificate08Block18Coeff3 t)+(upperCertificate08Weight19 a)*(upperCertificate08Block19Coeff3 t))))+(((upperCertificate08Weight20 a)*(upperCertificate08Block20Coeff3 t)+((upperCertificate08Weight21 a)*(upperCertificate08Block21Coeff3 t)+(upperCertificate08Weight22 a)*(upperCertificate08Block22Coeff3 t)))+(((upperCertificate08Weight23 a)*(upperCertificate08Block23Coeff3 t)+(upperCertificate08Weight24 a)*(upperCertificate08Block24Coeff3 t))+((upperCertificate08Weight25 a)*(upperCertificate08Block25Coeff3 t)+(upperCertificate08Weight26 a)*(upperCertificate08Block26Coeff3 t)))))) := by
  exact upperAtom08Coeff3_identity_source_value a t

end LeanVerification.PositiveDCompletion
