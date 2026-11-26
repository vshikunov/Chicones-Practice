import LeanVerification.PositiveDCompletion.UpperCertificate09Coefficient0Kernel
import LeanVerification.PositiveDCompletion.UpperCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperAtom09Coeff0_identity (a t : ℝ) :
    upperAtom09Coeff0 a t=(((((upperCertificate09Weight00 a)*(upperCertificate09Block00Coeff0 t)+((upperCertificate09Weight01 a)*(upperCertificate09Block01Coeff0 t)+(upperCertificate09Weight02 a)*(upperCertificate09Block02Coeff0 t)))+(((upperCertificate09Weight03 a)*(upperCertificate09Block03Coeff0 t)+(upperCertificate09Weight04 a)*(upperCertificate09Block04Coeff0 t))+((upperCertificate09Weight05 a)*(upperCertificate09Block05Coeff0 t)+(upperCertificate09Weight06 a)*(upperCertificate09Block06Coeff0 t))))+(((upperCertificate09Weight07 a)*(upperCertificate09Block07Coeff0 t)+((upperCertificate09Weight08 a)*(upperCertificate09Block08Coeff0 t)+(upperCertificate09Weight09 a)*(upperCertificate09Block09Coeff0 t)))+(((upperCertificate09Weight10 a)*(upperCertificate09Block10Coeff0 t)+(upperCertificate09Weight11 a)*(upperCertificate09Block11Coeff0 t))+((upperCertificate09Weight12 a)*(upperCertificate09Block12Coeff0 t)+(upperCertificate09Weight13 a)*(upperCertificate09Block13Coeff0 t)))))+((((upperCertificate09Weight14 a)*(upperCertificate09Block14Coeff0 t)+((upperCertificate09Weight15 a)*(upperCertificate09Block15Coeff0 t)+(upperCertificate09Weight16 a)*(upperCertificate09Block16Coeff0 t)))+(((upperCertificate09Weight17 a)*(upperCertificate09Block17Coeff0 t)+(upperCertificate09Weight18 a)*(upperCertificate09Block18Coeff0 t))+((upperCertificate09Weight19 a)*(upperCertificate09Block19Coeff0 t)+(upperCertificate09Weight20 a)*(upperCertificate09Block20Coeff0 t))))+(((upperCertificate09Weight21 a)*(upperCertificate09Block21Coeff0 t)+((upperCertificate09Weight22 a)*(upperCertificate09Block22Coeff0 t)+(upperCertificate09Weight23 a)*(upperCertificate09Block23Coeff0 t)))+(((upperCertificate09Weight24 a)*(upperCertificate09Block24Coeff0 t)+(upperCertificate09Weight25 a)*(upperCertificate09Block25Coeff0 t))+((upperCertificate09Weight26 a)*(upperCertificate09Block26Coeff0 t)+(upperCertificate09Weight27 a)*(upperCertificate09Block27Coeff0 t)))))) := by
  exact upperAtom09Coeff0_identity_source_value a t

end LeanVerification.PositiveDCompletion
