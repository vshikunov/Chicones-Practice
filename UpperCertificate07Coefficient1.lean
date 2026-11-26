import LeanVerification.PositiveDCompletion.UpperCertificate07Coefficient1Kernel
import LeanVerification.PositiveDCompletion.UpperCertificate07Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperAtom07Coeff1_identity (a t : ℝ) :
    upperAtom07Coeff1 a t=(((((upperCertificate07Weight00 a)*(upperCertificate07Block00Coeff1 t)+(upperCertificate07Weight01 a)*(upperCertificate07Block01Coeff1 t))+((upperCertificate07Weight02 a)*(upperCertificate07Block02Coeff1 t)+((upperCertificate07Weight03 a)*(upperCertificate07Block03Coeff1 t)+(upperCertificate07Weight04 a)*(upperCertificate07Block04Coeff1 t))))+(((upperCertificate07Weight05 a)*(upperCertificate07Block05Coeff1 t)+(upperCertificate07Weight06 a)*(upperCertificate07Block06Coeff1 t))+((upperCertificate07Weight07 a)*(upperCertificate07Block07Coeff1 t)+((upperCertificate07Weight08 a)*(upperCertificate07Block08Coeff1 t)+(upperCertificate07Weight09 a)*(upperCertificate07Block09Coeff1 t)))))+((((upperCertificate07Weight10 a)*(upperCertificate07Block10Coeff1 t)+(upperCertificate07Weight11 a)*(upperCertificate07Block11Coeff1 t))+((upperCertificate07Weight12 a)*(upperCertificate07Block12Coeff1 t)+((upperCertificate07Weight13 a)*(upperCertificate07Block13Coeff1 t)+(upperCertificate07Weight14 a)*(upperCertificate07Block14Coeff1 t))))+(((upperCertificate07Weight15 a)*(upperCertificate07Block15Coeff1 t)+(upperCertificate07Weight16 a)*(upperCertificate07Block16Coeff1 t))+((upperCertificate07Weight17 a)*(upperCertificate07Block17Coeff1 t)+((upperCertificate07Weight18 a)*(upperCertificate07Block18Coeff1 t)+(upperCertificate07Weight19 a)*(upperCertificate07Block19Coeff1 t)))))) := by
  exact upperAtom07Coeff1_identity_source_value a t

end LeanVerification.PositiveDCompletion
