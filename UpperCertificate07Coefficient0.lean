import LeanVerification.PositiveDCompletion.UpperCertificate07Coefficient0Kernel
import LeanVerification.PositiveDCompletion.UpperCertificate07Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperAtom07Coeff0_identity (a t : ℝ) :
    upperAtom07Coeff0 a t=(((((upperCertificate07Weight00 a)*(upperCertificate07Block00Coeff0 t)+(upperCertificate07Weight01 a)*(upperCertificate07Block01Coeff0 t))+((upperCertificate07Weight02 a)*(upperCertificate07Block02Coeff0 t)+((upperCertificate07Weight03 a)*(upperCertificate07Block03Coeff0 t)+(upperCertificate07Weight04 a)*(upperCertificate07Block04Coeff0 t))))+(((upperCertificate07Weight05 a)*(upperCertificate07Block05Coeff0 t)+(upperCertificate07Weight06 a)*(upperCertificate07Block06Coeff0 t))+((upperCertificate07Weight07 a)*(upperCertificate07Block07Coeff0 t)+((upperCertificate07Weight08 a)*(upperCertificate07Block08Coeff0 t)+(upperCertificate07Weight09 a)*(upperCertificate07Block09Coeff0 t)))))+((((upperCertificate07Weight10 a)*(upperCertificate07Block10Coeff0 t)+(upperCertificate07Weight11 a)*(upperCertificate07Block11Coeff0 t))+((upperCertificate07Weight12 a)*(upperCertificate07Block12Coeff0 t)+((upperCertificate07Weight13 a)*(upperCertificate07Block13Coeff0 t)+(upperCertificate07Weight14 a)*(upperCertificate07Block14Coeff0 t))))+(((upperCertificate07Weight15 a)*(upperCertificate07Block15Coeff0 t)+(upperCertificate07Weight16 a)*(upperCertificate07Block16Coeff0 t))+((upperCertificate07Weight17 a)*(upperCertificate07Block17Coeff0 t)+((upperCertificate07Weight18 a)*(upperCertificate07Block18Coeff0 t)+(upperCertificate07Weight19 a)*(upperCertificate07Block19Coeff0 t)))))) := by
  exact upperAtom07Coeff0_identity_source_value a t

end LeanVerification.PositiveDCompletion
