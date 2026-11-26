import LeanVerification.PositiveDCompletion.UpperPolynomial08Clear
import LeanVerification.PositiveDCompletion.UpperPolynomial08Map0
import LeanVerification.PositiveDCompletion.UpperPolynomial08Map1
import LeanVerification.PositiveDCompletion.UpperPolynomial08Map2
import LeanVerification.PositiveDCompletion.UpperPolynomial08Map3
import LeanVerification.PositiveDCompletion.UpperPolynomial08Map4
import LeanVerification.PositiveDCompletion.UpperPolynomial08Map5
import LeanVerification.PositiveDCompletion.UpperPolynomial08Map6

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperNum08_map (a t z : ℝ) :
    upperCorrelated08 a (a+(1-a)*t) (a*z)=(1-a)^(4 : ℕ)*upperAtom08 a t z := by
  have h0 : upperNum08Coeff0 a (a+(1-a)*t)*(a+(1-a)*t)^(6 : ℕ)*(a*z)^(0 : ℕ)=(1-a)^(4 : ℕ)*upperAtom08Coeff0 a t*z^(0 : ℕ) := by
    rw [mul_pow,←mul_assoc,upperNum08Coeff0_map]
  have h1 : upperNum08Coeff1 a (a+(1-a)*t)*(a+(1-a)*t)^(5 : ℕ)*(a*z)^(1 : ℕ)=(1-a)^(4 : ℕ)*upperAtom08Coeff1 a t*z^(1 : ℕ) := by
    rw [mul_pow,←mul_assoc,upperNum08Coeff1_map]
  have h2 : upperNum08Coeff2 a (a+(1-a)*t)*(a+(1-a)*t)^(4 : ℕ)*(a*z)^(2 : ℕ)=(1-a)^(4 : ℕ)*upperAtom08Coeff2 a t*z^(2 : ℕ) := by
    rw [mul_pow,←mul_assoc,upperNum08Coeff2_map]
  have h3 : upperNum08Coeff3 a (a+(1-a)*t)*(a+(1-a)*t)^(3 : ℕ)*(a*z)^(3 : ℕ)=(1-a)^(4 : ℕ)*upperAtom08Coeff3 a t*z^(3 : ℕ) := by
    rw [mul_pow,←mul_assoc,upperNum08Coeff3_map]
  have h4 : upperNum08Coeff4 a (a+(1-a)*t)*(a+(1-a)*t)^(2 : ℕ)*(a*z)^(4 : ℕ)=(1-a)^(4 : ℕ)*upperAtom08Coeff4 a t*z^(4 : ℕ) := by
    rw [mul_pow,←mul_assoc,upperNum08Coeff4_map]
  have h5 : upperNum08Coeff5 a (a+(1-a)*t)*(a+(1-a)*t)^(1 : ℕ)*(a*z)^(5 : ℕ)=(1-a)^(4 : ℕ)*upperAtom08Coeff5 a t*z^(5 : ℕ) := by
    rw [mul_pow,←mul_assoc,upperNum08Coeff5_map]
  have h6 : upperNum08Coeff6 a (a+(1-a)*t)*(a+(1-a)*t)^(0 : ℕ)*(a*z)^(6 : ℕ)=(1-a)^(4 : ℕ)*upperAtom08Coeff6 a t*z^(6 : ℕ) := by
    rw [mul_pow,←mul_assoc,upperNum08Coeff6_map]
  unfold upperCorrelated08 upperAtom08
  rw [h0,h1,h2,h3,h4,h5,h6]
  ring

end LeanVerification.PositiveDCompletion
