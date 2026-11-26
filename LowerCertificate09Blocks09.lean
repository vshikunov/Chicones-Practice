import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks09Kernel
import LeanVerification.PositiveDCompletion.LowerCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCertificate09Block45_identity (t u : ℝ) :
    lowerCertificate09Block45 t u=(((lowerCertificate09Block45Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block45Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block45Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block45Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block45Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block45Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block45Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block45_identity_source_value t u

theorem lowerCertificate09Block45_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block45 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block45
  positivity

theorem lowerCertificate09Block46_identity (t u : ℝ) :
    lowerCertificate09Block46 t u=(((lowerCertificate09Block46Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block46Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block46Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block46Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block46Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block46Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block46Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block46_identity_source_value t u

theorem lowerCertificate09Block46_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block46 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block46
  positivity

theorem lowerCertificate09Block47_identity (t u : ℝ) :
    lowerCertificate09Block47 t u=(((lowerCertificate09Block47Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block47Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block47Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block47Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block47Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block47Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block47Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block47_identity_source_value t u

theorem lowerCertificate09Block47_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block47 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block47
  positivity

theorem lowerCertificate09Block48_identity (t u : ℝ) :
    lowerCertificate09Block48 t u=(((lowerCertificate09Block48Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block48Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block48Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block48Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block48Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block48Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block48Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block48_identity_source_value t u

theorem lowerCertificate09Block48_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block48 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block48
  positivity

theorem lowerCertificate09Block49_identity (t u : ℝ) :
    lowerCertificate09Block49 t u=(((lowerCertificate09Block49Coeff0 t)*u^(0 : ℕ)+((lowerCertificate09Block49Coeff1 t)*u^(1 : ℕ)+(lowerCertificate09Block49Coeff2 t)*u^(2 : ℕ)))+(((lowerCertificate09Block49Coeff3 t)*u^(3 : ℕ)+(lowerCertificate09Block49Coeff4 t)*u^(4 : ℕ))+((lowerCertificate09Block49Coeff5 t)*u^(5 : ℕ)+(lowerCertificate09Block49Coeff6 t)*u^(6 : ℕ)))) := by
  exact lowerCertificate09Block49_identity_source_value t u

theorem lowerCertificate09Block49_pos {t u : ℝ} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerCertificate09Block49 t u := by
  have htc : 0<1-t := by linarith
  have huc : 0<1-u := by linarith
  unfold lowerCertificate09Block49
  positivity

end LeanVerification.PositiveDCompletion
