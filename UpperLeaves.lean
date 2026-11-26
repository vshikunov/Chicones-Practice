import LeanVerification.PositiveDCompletion.PoleSigns
import LeanVerification.PositiveDCompletion.SecantGeometry
import LeanVerification.PositiveDCompletion.UpperCertificate00
import LeanVerification.PositiveDCompletion.UpperCertificate01
import LeanVerification.PositiveDCompletion.UpperCertificate02
import LeanVerification.PositiveDCompletion.UpperCertificate03
import LeanVerification.PositiveDCompletion.UpperCertificate04
import LeanVerification.PositiveDCompletion.UpperCertificate05
import LeanVerification.PositiveDCompletion.UpperCertificate06
import LeanVerification.PositiveDCompletion.UpperCertificate07
import LeanVerification.PositiveDCompletion.UpperCertificate08
import LeanVerification.PositiveDCompletion.UpperCertificate09

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion

theorem upper_leaf_signs {a f rho : ℝ} (ha : 0<a) (hau : a<1)
    (haf : a<f) (hf : f<1) (hr : 0<rho) (hru : rho<1) (hp : f*rho<a) :
    LeafSigns 1 a f rho := by
  constructor
  · simpa only [one_mul] using upperNum00_pos ha hau haf hf hr hru
  · simpa only [one_mul] using upperNum01_pos ha hau haf hf hr hru
  · simpa only [one_mul] using upperNum02_pos ha hau haf hf hr hru
  · simpa only [one_mul] using upperNum03_pos ha hau haf hf hr hru
  · simpa only [one_mul] using upperNum04_pos ha hau haf hf hr hru
  · simpa only [one_mul] using upperNum05_pos ha hau haf hf hr hru
  · simpa only [one_mul] using upperNum06_pos ha hau haf hf hr hru
  · simpa only [one_mul] using upperNum07_pos ha hau haf hf hr hru
  · simpa only [one_mul] using upperNum08_pos ha hau haf hf hr hru hp
  · simpa only [one_mul] using upperNum09_pos ha hau haf hf hr hru hp

theorem actual_upper_pole_signs {a q : ℝ} (ha : 0<a) (hau : a<1) (hq : 0<q) :
    PoleCoefficientSigns a (secantF a q) (secantRho a q) := by
  have hf := secantF_bounds ha hau hq
  have hr := secantRho_bounds ha hau hq
  exact upper_pole_coefficient_signs ha hf.1 hf.2 hr.1 hr.2
    (upper_leaf_signs ha hau hf.1 hf.2 hr.1 hr.2 (secant_product_lt ha hau hq))

end LeanVerification.PositiveDCompletion
