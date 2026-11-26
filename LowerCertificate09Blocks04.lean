import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks04Kernel
import LeanVerification.PositiveDCompletion.LowerCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCertificate09Block20_identity (t u : ℝ) :
    lowerCertificate09Block20 t u=(((lowerCertificate09Block20Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block20Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block20Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block20Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block20Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block20Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block20Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block20_identity_source_value t u

theorem lowerCertificate09Block20_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block20 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block20
  positivity

theorem lowerCertificate09Block21_identity (t u : ℝ) :
    lowerCertificate09Block21 t u=(((lowerCertificate09Block21Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block21Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block21Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block21Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block21Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block21Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block21Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block21_identity_source_value t u

theorem lowerCertificate09Block21_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block21 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block21
  positivity

theorem lowerCertificate09Block22_identity (t u : ℝ) :
    lowerCertificate09Block22 t u=(((lowerCertificate09Block22Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block22Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block22Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block22Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block22Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block22Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block22Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block22_identity_source_value t u

theorem lowerCertificate09Block22_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block22 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block22
  positivity

theorem lowerCertificate09Block23_identity (t u : ℝ) :
    lowerCertificate09Block23 t u=(((lowerCertificate09Block23Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block23Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block23Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block23Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block23Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block23Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block23Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block23_identity_source_value t u

theorem lowerCertificate09Block23_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block23 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block23
  positivity

theorem lowerCertificate09Block24_identity (t u : ℝ) :
    lowerCertificate09Block24 t u=(((lowerCertificate09Block24Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block24Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block24Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block24Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block24Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block24Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block24Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block24_identity_source_value t u

theorem lowerCertificate09Block24_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block24 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block24
  positivity

end LeanVerification.PositiveDCompletion
