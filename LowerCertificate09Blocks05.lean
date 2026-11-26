import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks05Kernel
import LeanVerification.PositiveDCompletion.LowerCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCertificate09Block25_identity (t u : ℝ) :
    lowerCertificate09Block25 t u=(((lowerCertificate09Block25Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block25Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block25Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block25Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block25Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block25Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block25Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block25_identity_source_value t u

theorem lowerCertificate09Block25_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block25 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block25
  positivity

theorem lowerCertificate09Block26_identity (t u : ℝ) :
    lowerCertificate09Block26 t u=(((lowerCertificate09Block26Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block26Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block26Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block26Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block26Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block26Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block26Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block26_identity_source_value t u

theorem lowerCertificate09Block26_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block26 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block26
  positivity

theorem lowerCertificate09Block27_identity (t u : ℝ) :
    lowerCertificate09Block27 t u=(((lowerCertificate09Block27Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block27Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block27Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block27Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block27Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block27Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block27Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block27_identity_source_value t u

theorem lowerCertificate09Block27_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block27 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block27
  positivity

theorem lowerCertificate09Block28_identity (t u : ℝ) :
    lowerCertificate09Block28 t u=(((lowerCertificate09Block28Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block28Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block28Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block28Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block28Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block28Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block28Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block28_identity_source_value t u

theorem lowerCertificate09Block28_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block28 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block28
  positivity

theorem lowerCertificate09Block29_identity (t u : ℝ) :
    lowerCertificate09Block29 t u=(((lowerCertificate09Block29Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block29Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block29Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block29Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block29Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block29Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block29Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block29_identity_source_value t u

theorem lowerCertificate09Block29_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block29 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block29
  positivity

end LeanVerification.PositiveDCompletion
