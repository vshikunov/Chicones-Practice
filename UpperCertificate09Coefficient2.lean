import LeanVerification.PositiveDCompletion.UpperCertificate09Coefficient2Kernel
import LeanVerification.PositiveDCompletion.UpperCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperAtom09Coeff2_identity (a t : ℝ) :
    upperAtom09Coeff2 a t=(((((upperCertificate09Weight00 a)*(upperCertificate09Block00Coeff2 t)+((upperCertificate09Weight01 a)*(upperCertificate09Block01Coeff2 t)+(upperCertificate09Weight02 a)*(upperCertificate09Block02Coeff2 t)))+(((upperCertificate09Weight03 a)*(upperCertificate09Block03Coeff2 t)+(upperCertificate09Weight04 a)*(upperCertificate09Block04Coeff2 t))+((upperCertificate09Weight05 a)*(upperCertificate09Block05Coeff2 t)+(upperCertificate09Weight06 a)*(upperCertificate09Block06Coeff2 t))))+(((upperCertificate09Weight07 a)*(upperCertificate09Block07Coeff2 t)+((upperCertificate09Weight08 a)*(upperCertificate09Block08Coeff2 t)+(upperCertificate09Weight09 a)*(upperCertificate09Block09Coeff2 t)))+(((upperCertificate09Weight10 a)*(upperCertificate09Block10Coeff2 t)+(upperCertificate09Weight11 a)*(upperCertificate09Block11Coeff2 t))+((upperCertificate09Weight12 a)*(upperCertificate09Block12Coeff2 t)+(upperCertificate09Weight13 a)*(upperCertificate09Block13Coeff2 t)))))+((((upperCertificate09Weight14 a)*(upperCertificate09Block14Coeff2 t)+((upperCertificate09Weight15 a)*(upperCertificate09Block15Coeff2 t)+(upperCertificate09Weight16 a)*(upperCertificate09Block16Coeff2 t)))+(((upperCertificate09Weight17 a)*(upperCertificate09Block17Coeff2 t)+(upperCertificate09Weight18 a)*(upperCertificate09Block18Coeff2 t))+((upperCertificate09Weight19 a)*(upperCertificate09Block19Coeff2 t)+(upperCertificate09Weight20 a)*(upperCertificate09Block20Coeff2 t))))+(((upperCertificate09Weight21 a)*(upperCertificate09Block21Coeff2 t)+((upperCertificate09Weight22 a)*(upperCertificate09Block22Coeff2 t)+(upperCertificate09Weight23 a)*(upperCertificate09Block23Coeff2 t)))+(((upperCertificate09Weight24 a)*(upperCertificate09Block24Coeff2 t)+(upperCertificate09Weight25 a)*(upperCertificate09Block25Coeff2 t))+((upperCertificate09Weight26 a)*(upperCertificate09Block26Coeff2 t)+(upperCertificate09Weight27 a)*(upperCertificate09Block27Coeff2 t)))))) := by
  exact upperAtom09Coeff2_identity_source_value a t

end LeanVerification.PositiveDCompletion
