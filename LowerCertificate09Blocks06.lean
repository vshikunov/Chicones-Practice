import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks06Kernel
import LeanVerification.PositiveDCompletion.LowerCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCertificate09Block30_identity (t u : ℝ) :
    lowerCertificate09Block30 t u=(((lowerCertificate09Block30Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block30Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block30Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block30Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block30Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block30Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block30Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block30_identity_source_value t u

theorem lowerCertificate09Block30_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block30 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block30
  positivity

theorem lowerCertificate09Block31_identity (t u : ℝ) :
    lowerCertificate09Block31 t u=(((lowerCertificate09Block31Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block31Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block31Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block31Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block31Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block31Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block31Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block31_identity_source_value t u

theorem lowerCertificate09Block31_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block31 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block31
  positivity

theorem lowerCertificate09Block32_identity (t u : ℝ) :
    lowerCertificate09Block32 t u=(((lowerCertificate09Block32Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block32Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block32Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block32Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block32Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block32Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block32Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block32_identity_source_value t u

theorem lowerCertificate09Block32_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block32 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block32
  positivity

theorem lowerCertificate09Block33_identity (t u : ℝ) :
    lowerCertificate09Block33 t u=(((lowerCertificate09Block33Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block33Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block33Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block33Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block33Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block33Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block33Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block33_identity_source_value t u

theorem lowerCertificate09Block33_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block33 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block33
  positivity

theorem lowerCertificate09Block34_identity (t u : ℝ) :
    lowerCertificate09Block34 t u=(((lowerCertificate09Block34Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block34Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block34Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block34Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block34Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block34Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block34Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block34_identity_source_value t u

theorem lowerCertificate09Block34_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block34 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block34
  positivity

end LeanVerification.PositiveDCompletion
