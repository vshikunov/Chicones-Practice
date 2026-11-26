import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks03Kernel
import LeanVerification.PositiveDCompletion.LowerCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCertificate09Block15_identity (t u : ℝ) :
    lowerCertificate09Block15 t u=(((lowerCertificate09Block15Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block15Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block15Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block15Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block15Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block15Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block15Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block15_identity_source_value t u

theorem lowerCertificate09Block15_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block15 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block15
  positivity

theorem lowerCertificate09Block16_identity (t u : ℝ) :
    lowerCertificate09Block16 t u=(((lowerCertificate09Block16Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block16Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block16Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block16Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block16Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block16Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block16Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block16_identity_source_value t u

theorem lowerCertificate09Block16_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block16 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block16
  positivity

theorem lowerCertificate09Block17_identity (t u : ℝ) :
    lowerCertificate09Block17 t u=(((lowerCertificate09Block17Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block17Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block17Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block17Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block17Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block17Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block17Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block17_identity_source_value t u

theorem lowerCertificate09Block17_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block17 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block17
  positivity

theorem lowerCertificate09Block18_identity (t u : ℝ) :
    lowerCertificate09Block18 t u=(((lowerCertificate09Block18Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block18Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block18Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block18Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block18Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block18Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block18Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block18_identity_source_value t u

theorem lowerCertificate09Block18_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block18 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block18
  positivity

theorem lowerCertificate09Block19_identity (t u : ℝ) :
    lowerCertificate09Block19 t u=(((lowerCertificate09Block19Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block19Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block19Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block19Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block19Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block19Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block19Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block19_identity_source_value t u

theorem lowerCertificate09Block19_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block19 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block19
  positivity

end LeanVerification.PositiveDCompletion
