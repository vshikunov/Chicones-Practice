import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks07Kernel
import LeanVerification.PositiveDCompletion.LowerCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCertificate09Block35_identity (t u : ℝ) :
    lowerCertificate09Block35 t u=(((lowerCertificate09Block35Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block35Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block35Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block35Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block35Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block35Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block35Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block35_identity_source_value t u

theorem lowerCertificate09Block35_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block35 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block35
  positivity

theorem lowerCertificate09Block36_identity (t u : ℝ) :
    lowerCertificate09Block36 t u=(((lowerCertificate09Block36Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block36Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block36Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block36Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block36Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block36Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block36Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block36_identity_source_value t u

theorem lowerCertificate09Block36_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block36 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block36
  positivity

theorem lowerCertificate09Block37_identity (t u : ℝ) :
    lowerCertificate09Block37 t u=(((lowerCertificate09Block37Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block37Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block37Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block37Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block37Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block37Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block37Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block37_identity_source_value t u

theorem lowerCertificate09Block37_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block37 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block37
  positivity

theorem lowerCertificate09Block38_identity (t u : ℝ) :
    lowerCertificate09Block38 t u=(((lowerCertificate09Block38Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block38Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block38Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block38Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block38Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block38Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block38Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block38_identity_source_value t u

theorem lowerCertificate09Block38_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block38 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block38
  positivity

theorem lowerCertificate09Block39_identity (t u : ℝ) :
    lowerCertificate09Block39 t u=(((lowerCertificate09Block39Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block39Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block39Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block39Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block39Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block39Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block39Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block39_identity_source_value t u

theorem lowerCertificate09Block39_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block39 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block39
  positivity

end LeanVerification.PositiveDCompletion
