import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks02Kernel
import LeanVerification.PositiveDCompletion.LowerCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCertificate09Block10_identity (t u : ℝ) :
    lowerCertificate09Block10 t u=(((lowerCertificate09Block10Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block10Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block10Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block10Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block10Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block10Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block10Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block10_identity_source_value t u

theorem lowerCertificate09Block10_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block10 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block10
  positivity

theorem lowerCertificate09Block11_identity (t u : ℝ) :
    lowerCertificate09Block11 t u=(((lowerCertificate09Block11Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block11Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block11Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block11Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block11Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block11Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block11Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block11_identity_source_value t u

theorem lowerCertificate09Block11_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block11 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block11
  positivity

theorem lowerCertificate09Block12_identity (t u : ℝ) :
    lowerCertificate09Block12 t u=(((lowerCertificate09Block12Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block12Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block12Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block12Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block12Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block12Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block12Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block12_identity_source_value t u

theorem lowerCertificate09Block12_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block12 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block12
  positivity

theorem lowerCertificate09Block13_identity (t u : ℝ) :
    lowerCertificate09Block13 t u=(((lowerCertificate09Block13Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block13Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block13Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block13Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block13Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block13Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block13Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block13_identity_source_value t u

theorem lowerCertificate09Block13_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block13 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block13
  positivity

theorem lowerCertificate09Block14_identity (t u : ℝ) :
    lowerCertificate09Block14 t u=(((lowerCertificate09Block14Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block14Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block14Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block14Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block14Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block14Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block14Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block14_identity_source_value t u

theorem lowerCertificate09Block14_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block14 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block14
  positivity

end LeanVerification.PositiveDCompletion
