import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks01Kernel
import LeanVerification.PositiveDCompletion.LowerCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCertificate09Block05_identity (t u : ℝ) :
    lowerCertificate09Block05 t u=(((lowerCertificate09Block05Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block05Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block05Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block05Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block05Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block05Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block05Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block05_identity_source_value t u

theorem lowerCertificate09Block05_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block05 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block05
  positivity

theorem lowerCertificate09Block06_identity (t u : ℝ) :
    lowerCertificate09Block06 t u=(((lowerCertificate09Block06Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block06Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block06Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block06Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block06Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block06Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block06Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block06_identity_source_value t u

theorem lowerCertificate09Block06_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block06 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block06
  positivity

theorem lowerCertificate09Block07_identity (t u : ℝ) :
    lowerCertificate09Block07 t u=(((lowerCertificate09Block07Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block07Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block07Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block07Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block07Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block07Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block07Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block07_identity_source_value t u

theorem lowerCertificate09Block07_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block07 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block07
  positivity

theorem lowerCertificate09Block08_identity (t u : ℝ) :
    lowerCertificate09Block08 t u=(((lowerCertificate09Block08Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block08Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block08Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block08Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block08Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block08Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block08Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block08_identity_source_value t u

theorem lowerCertificate09Block08_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block08 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block08
  positivity

theorem lowerCertificate09Block09_identity (t u : ℝ) :
    lowerCertificate09Block09 t u=(((lowerCertificate09Block09Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block09Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block09Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block09Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block09Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block09Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block09Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block09_identity_source_value t u

theorem lowerCertificate09Block09_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block09 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block09
  positivity

end LeanVerification.PositiveDCompletion
