import LeanVerification.PositiveDCompletion.UpperCertificate09Coefficient3Kernel
import LeanVerification.PositiveDCompletion.UpperCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperAtom09Coeff3_identity (a t : ℝ) :
    upperAtom09Coeff3 a t=(((((upperCertificate09Weight00 a)*(upperCertificate09Block00Coeff3 t)+((upperCertificate09Weight01 a)*(upperCertificate09Block01Coeff3 t)+(upperCertificate09Weight02 a)*(upperCertificate09Block02Coeff3 t)))+(((upperCertificate09Weight03 a)*(upperCertificate09Block03Coeff3 t)+(upperCertificate09Weight04 a)*(upperCertificate09Block04Coeff3 t))+((upperCertificate09Weight05 a)*(upperCertificate09Block05Coeff3 t)+(upperCertificate09Weight06 a)*(upperCertificate09Block06Coeff3 t))))+(((upperCertificate09Weight07 a)*(upperCertificate09Block07Coeff3 t)+((upperCertificate09Weight08 a)*(upperCertificate09Block08Coeff3 t)+(upperCertificate09Weight09 a)*(upperCertificate09Block09Coeff3 t)))+(((upperCertificate09Weight10 a)*(upperCertificate09Block10Coeff3 t)+(upperCertificate09Weight11 a)*(upperCertificate09Block11Coeff3 t))+((upperCertificate09Weight12 a)*(upperCertificate09Block12Coeff3 t)+(upperCertificate09Weight13 a)*(upperCertificate09Block13Coeff3 t)))))+((((upperCertificate09Weight14 a)*(upperCertificate09Block14Coeff3 t)+((upperCertificate09Weight15 a)*(upperCertificate09Block15Coeff3 t)+(upperCertificate09Weight16 a)*(upperCertificate09Block16Coeff3 t)))+(((upperCertificate09Weight17 a)*(upperCertificate09Block17Coeff3 t)+(upperCertificate09Weight18 a)*(upperCertificate09Block18Coeff3 t))+((upperCertificate09Weight19 a)*(upperCertificate09Block19Coeff3 t)+(upperCertificate09Weight20 a)*(upperCertificate09Block20Coeff3 t))))+(((upperCertificate09Weight21 a)*(upperCertificate09Block21Coeff3 t)+((upperCertificate09Weight22 a)*(upperCertificate09Block22Coeff3 t)+(upperCertificate09Weight23 a)*(upperCertificate09Block23Coeff3 t)))+(((upperCertificate09Weight24 a)*(upperCertificate09Block24Coeff3 t)+(upperCertificate09Weight25 a)*(upperCertificate09Block25Coeff3 t))+((upperCertificate09Weight26 a)*(upperCertificate09Block26Coeff3 t)+(upperCertificate09Weight27 a)*(upperCertificate09Block27Coeff3 t)))))) := by
  exact upperAtom09Coeff3_identity_source_value a t

end LeanVerification.PositiveDCompletion
