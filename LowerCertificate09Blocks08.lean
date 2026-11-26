import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks08Kernel
import LeanVerification.PositiveDCompletion.LowerCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCertificate09Block40_identity (t u : ℝ) :
    lowerCertificate09Block40 t u=(((lowerCertificate09Block40Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block40Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block40Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block40Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block40Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block40Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block40Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block40_identity_source_value t u

theorem lowerCertificate09Block40_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block40 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block40
  positivity

theorem lowerCertificate09Block41_identity (t u : ℝ) :
    lowerCertificate09Block41 t u=(((lowerCertificate09Block41Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block41Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block41Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block41Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block41Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block41Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block41Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block41_identity_source_value t u

theorem lowerCertificate09Block41_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block41 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block41
  positivity

theorem lowerCertificate09Block42_identity (t u : ℝ) :
    lowerCertificate09Block42 t u=(((lowerCertificate09Block42Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block42Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block42Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block42Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block42Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block42Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block42Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block42_identity_source_value t u

theorem lowerCertificate09Block42_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block42 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block42
  positivity

theorem lowerCertificate09Block43_identity (t u : ℝ) :
    lowerCertificate09Block43 t u=(((lowerCertificate09Block43Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block43Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block43Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block43Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block43Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block43Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block43Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block43_identity_source_value t u

theorem lowerCertificate09Block43_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block43 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block43
  positivity

theorem lowerCertificate09Block44_identity (t u : ℝ) :
    lowerCertificate09Block44 t u=(((lowerCertificate09Block44Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block44Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block44Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block44Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block44Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block44Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block44Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block44_identity_source_value t u

theorem lowerCertificate09Block44_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block44 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block44
  positivity

end LeanVerification.PositiveDCompletion
