import LeanVerification.PositiveDCompletion.UpperCertificate07Coefficient4Kernel
import LeanVerification.PositiveDCompletion.UpperCertificate07Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperAtom07Coeff4_identity (a t : ℝ) :
    upperAtom07Coeff4 a t=(((((upperCertificate07Weight00 a)*(upperCertificate07Block00Coeff4 t)+(upperCertificate07Weight01 a)*(upperCertificate07Block01Coeff4 t))+((upperCertificate07Weight02 a)*(upperCertificate07Block02Coeff4 t)+((upperCertificate07Weight03 a)*(upperCertificate07Block03Coeff4 t)+(upperCertificate07Weight04 a)*(upperCertificate07Block04Coeff4 t))))+(((upperCertificate07Weight05 a)*(upperCertificate07Block05Coeff4 t)+(upperCertificate07Weight06 a)*(upperCertificate07Block06Coeff4 t))+((upperCertificate07Weight07 a)*(upperCertificate07Block07Coeff4 t)+((upperCertificate07Weight08 a)*(upperCertificate07Block08Coeff4 t)+(upperCertificate07Weight09 a)*(upperCertificate07Block09Coeff4 t)))))+((((upperCertificate07Weight10 a)*(upperCertificate07Block10Coeff4 t)+(upperCertificate07Weight11 a)*(upperCertificate07Block11Coeff4 t))+((upperCertificate07Weight12 a)*(upperCertificate07Block12Coeff4 t)+((upperCertificate07Weight13 a)*(upperCertificate07Block13Coeff4 t)+(upperCertificate07Weight14 a)*(upperCertificate07Block14Coeff4 t))))+(((upperCertificate07Weight15 a)*(upperCertificate07Block15Coeff4 t)+(upperCertificate07Weight16 a)*(upperCertificate07Block16Coeff4 t))+((upperCertificate07Weight17 a)*(upperCertificate07Block17Coeff4 t)+((upperCertificate07Weight18 a)*(upperCertificate07Block18Coeff4 t)+(upperCertificate07Weight19 a)*(upperCertificate07Block19Coeff4 t)))))) := by
  exact upperAtom07Coeff4_identity_source_value a t

end LeanVerification.PositiveDCompletion
