import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks10Kernel
import LeanVerification.PositiveDCompletion.LowerCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCertificate09Block50_identity (t u : ℝ) :
    lowerCertificate09Block50 t u=(((lowerCertificate09Block50Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block50Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block50Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block50Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block50Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block50Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block50Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block50_identity_source_value t u

theorem lowerCertificate09Block50_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block50 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block50
  positivity

theorem lowerCertificate09Block51_identity (t u : ℝ) :
    lowerCertificate09Block51 t u=(((lowerCertificate09Block51Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block51Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block51Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block51Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block51Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block51Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block51Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block51_identity_source_value t u

theorem lowerCertificate09Block51_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block51 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block51
  positivity

end LeanVerification.PositiveDCompletion
