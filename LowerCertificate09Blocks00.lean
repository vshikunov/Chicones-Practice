import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks00Kernel
import LeanVerification.PositiveDCompletion.LowerCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCertificate09Block00_identity (t u : ℝ) :
    lowerCertificate09Block00 t u=(((lowerCertificate09Block00Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block00Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block00Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block00Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block00Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block00Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block00Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block00_identity_source_value t u

theorem lowerCertificate09Block00_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block00 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block00
  positivity

theorem lowerCertificate09Block01_identity (t u : ℝ) :
    lowerCertificate09Block01 t u=(((lowerCertificate09Block01Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block01Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block01Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block01Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block01Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block01Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block01Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block01_identity_source_value t u

theorem lowerCertificate09Block01_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block01 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block01
  positivity

theorem lowerCertificate09Block02_identity (t u : ℝ) :
    lowerCertificate09Block02 t u=(((lowerCertificate09Block02Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block02Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block02Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block02Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block02Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block02Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block02Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block02_identity_source_value t u

theorem lowerCertificate09Block02_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block02 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block02
  positivity

theorem lowerCertificate09Block03_identity (t u : ℝ) :
    lowerCertificate09Block03 t u=(((lowerCertificate09Block03Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block03Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block03Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block03Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block03Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block03Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block03Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block03_identity_source_value t u

theorem lowerCertificate09Block03_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block03 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block03
  positivity

theorem lowerCertificate09Block04_identity (t u : ℝ) :
    lowerCertificate09Block04 t u=(((lowerCertificate09Block04Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block04Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block04Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block04Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block04Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block04Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block04Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block04_identity_source_value t u

theorem lowerCertificate09Block04_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block04 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block04
  positivity

end LeanVerification.PositiveDCompletion
