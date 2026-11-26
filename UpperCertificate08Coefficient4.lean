import LeanVerification.PositiveDCompletion.UpperCertificate08Coefficient4Kernel
import LeanVerification.PositiveDCompletion.UpperCertificate08Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperAtom08Coeff4_identity (a t : ℝ) :
    upperAtom08Coeff4 a t=(((((upperCertificate08Weight00 a)*(upperCertificate08Block00Coeff4 t)+((upperCertificate08Weight01 a)*(upperCertificate08Block01Coeff4 t)+(upperCertificate08Weight02 a)*(upperCertificate08Block02Coeff4 t)))+((upperCertificate08Weight03 a)*(upperCertificate08Block03Coeff4 t)+((upperCertificate08Weight04 a)*(upperCertificate08Block04Coeff4 t)+(upperCertificate08Weight05 a)*(upperCertificate08Block05Coeff4 t))))+(((upperCertificate08Weight06 a)*(upperCertificate08Block06Coeff4 t)+((upperCertificate08Weight07 a)*(upperCertificate08Block07Coeff4 t)+(upperCertificate08Weight08 a)*(upperCertificate08Block08Coeff4 t)))+(((upperCertificate08Weight09 a)*(upperCertificate08Block09Coeff4 t)+(upperCertificate08Weight10 a)*(upperCertificate08Block10Coeff4 t))+((upperCertificate08Weight11 a)*(upperCertificate08Block11Coeff4 t)+(upperCertificate08Weight12 a)*(upperCertificate08Block12Coeff4 t)))))+((((upperCertificate08Weight13 a)*(upperCertificate08Block13Coeff4 t)+((upperCertificate08Weight14 a)*(upperCertificate08Block14Coeff4 t)+(upperCertificate08Weight15 a)*(upperCertificate08Block15Coeff4 t)))+(((upperCertificate08Weight16 a)*(upperCertificate08Block16Coeff4 t)+(upperCertificate08Weight17 a)*(upperCertificate08Block17Coeff4 t))+((upperCertificate08Weight18 a)*(upperCertificate08Block18Coeff4 t)+(upperCertificate08Weight19 a)*(upperCertificate08Block19Coeff4 t))))+(((upperCertificate08Weight20 a)*(upperCertificate08Block20Coeff4 t)+((upperCertificate08Weight21 a)*(upperCertificate08Block21Coeff4 t)+(upperCertificate08Weight22 a)*(upperCertificate08Block22Coeff4 t)))+(((upperCertificate08Weight23 a)*(upperCertificate08Block23Coeff4 t)+(upperCertificate08Weight24 a)*(upperCertificate08Block24Coeff4 t))+((upperCertificate08Weight25 a)*(upperCertificate08Block25Coeff4 t)+(upperCertificate08Weight26 a)*(upperCertificate08Block26Coeff4 t)))))) := by
  exact upperAtom08Coeff4_identity_source_value a t

end LeanVerification.PositiveDCompletion
