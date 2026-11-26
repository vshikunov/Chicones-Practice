import LeanVerification.PositiveDCompletion.SignedEnergy
import LeanVerification.ReflectedWedgeCompletion.RawStiffnessJets
import LeanVerification.ReflectedWedgeCompletion.WidthJetIdentities
import LeanVerification.PositiveDCompletion.WidthCriterion

noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.PositiveDCompletion
open Loud ReflectedCompletion ReflectedWedgeCompletion
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000

def saddleU (D F h : ℝ) : ℝ :=
  secantEnergyRatio (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h)
def saddleK (D F h : ℝ) : ℝ :=
  jetK (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h)
def saddleCurvature (D F h : ℝ) : ℝ :=
  jetCurvature (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h)

theorem secant_A_sign {a q : ℝ} (ha : 0<a) (ha1 : a≠1) (hq : 0<q) :
    0<((secantF a q)^2-a^2*secantRho a q)*(1-a^2*secantRho a q) := by
  rcases lt_or_gt_of_ne ha1 with hl|hu
  · have hf := secantF_bounds ha hl hq
    have hr := secantRho_bounds ha hl hq
    have hA : 0<(secantF a q)^2-a^2*secantRho a q := by
      have hm := mul_lt_mul_of_pos_left hr.2 (sq_pos_of_pos ha)
      nlinarith
    exact mul_pos hA (secant_g_pos ha hl hq)
  · obtain ⟨hf,hfa,hr⟩ := secant_lower_bounds hu hq
    have hm := mul_lt_mul_of_pos_left hr (sq_pos_of_pos ha)
    have hA : (secantF a q)^2-a^2*secantRho a q<0 := by nlinarith
    have hg : 1-a^2*secantRho a q<0 := by nlinarith
    exact mul_pos_of_neg_of_neg hA hg

theorem actual_signed_denominators {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    lowerPhysicalA F≠0 ∧ 1+wedgeF D F h≠0 ∧ 1+saddleOmega D F h≠0 ∧
      (wedgeF D F h)^2-(lowerPhysicalA F)^2*wedgeRho D F h≠0 ∧
      transportN (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h)≠0 := by
  have ha := (positiveD_parameter_bounds hD hF0 hF1).1
  have hF : 0<F := by linarith
  have hq := wedgeLogSecant_pos hF hh
  have hf := secantF_pos ha hq
  change 0<wedgeF D F h at hf
  have hA := secant_A_sign ha (lowerPhysicalA_ne_one hF hhalf) hq
  change 0<((wedgeF D F h)^2-(lowerPhysicalA F)^2*wedgeRho D F h)*
    (1-(lowerPhysicalA F)^2*wedgeRho D F h) at hA
  have hN := physical_transportN_sign hD hF0 hF1 hhalf hh
  refine ⟨ha.ne',by linarith,by linarith [saddleOmega_lt_neg_one hD hF0 hF1 hh],?_,?_⟩
  · intro he
    rw [he,zero_mul] at hA
    linarith
  · intro he
    rw [he,zero_mul] at hN
    linarith

theorem hasDerivAt_saddleU {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    HasDerivAt (saddleU D F) (wedgeRate D F h*(saddleK D F h-2*saddleU D F h)) h := by
  obtain ⟨ha,hf,ho,hA,hN⟩ := actual_signed_denominators hD hF0 hF1 hhalf hh
  obtain ⟨hff,hrr,hww⟩ := actual_signed_secant_transport hD hF0 hF1 hhalf hh
  exact secantEnergyRatio_hasDerivAt ha hf ho hA hN hff hrr hww

theorem hasDerivAt_saddleK {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    HasDerivAt (saddleK D F) (-wedgeRate D F h*saddleCurvature D F h) h := by
  obtain ⟨ha,hf,ho,hA,hN⟩ := actual_signed_denominators hD hF0 hF1 hhalf hh
  obtain ⟨hff,hrr,hww⟩ := actual_signed_secant_transport hD hF0 hF1 hhalf hh
  exact jetK_hasDerivAt ha hf ho hA hN hff hrr hww

theorem physical_stiffness_identity {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    1/(wedgeEnergyScale D F*lowerPhysicalD D)=
      wedgeWidth D F h*deriv (wedgeWidth D F) h*saddleK D F h := by
  exact widthjet_stiffness_identity (isOpen_admissibleEnergy D F) hh (analyticAt_wedgeWidth hh)
    (wedgeWidth_pos (by linarith : 0<F) hh).ne' (hasDerivAt_wedgeNormalizedEnergy D F h)
    (hasDerivAt_saddleU hD hF0 hF1 hhalf hh)
    (fun t ht => actual_signed_energy_width_identity hD hF0 hF1 hhalf ht)

theorem saddleK_pos {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) : 0<saddleK D F h := by
  have hc := one_div_pos.mpr (positiveD_parameter_bounds hD hF0 hF1).2.2.2
  rw [physical_stiffness_identity hD hF0 hF1 hhalf hh] at hc
  exact pos_of_mul_pos_right hc (mul_pos (wedgeWidth_pos (by linarith : 0<F) hh)
    (wedgeWidth_deriv_pos (by linarith : 0<F) hh)).le

theorem physical_curvature_identity {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    ((deriv (wedgeWidth D F) h)^2+wedgeWidth D F h*deriv (deriv (wedgeWidth D F)) h)*saddleK D F h=
      (deriv (wedgeWidth D F) h)^2*saddleCurvature D F h := by
  exact widthjet_curvature_identity (isOpen_admissibleEnergy D F) hh (analyticAt_wedgeWidth hh)
    (wedgeWidth_pos (by linarith : 0<F) hh).ne'
    (by simpa only [wedgeRate,neg_div] using hasDerivAt_saddleK hD hF0 hF1 hhalf hh)
    (fun t ht => physical_stiffness_identity hD hF0 hF1 hhalf ht)

theorem width_schwarz_of_signed_curvature {D F h RX : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h)
    (hPhi : HasDerivAt (saddleCurvature D F) (wedgeRate D F h*(RX-saddleCurvature D F h)) h)
    (hRX : 0<RX)
    (hchi : 0<(deriv (wedgeWidth D F) h)^2+wedgeWidth D F h*deriv (deriv (wedgeWidth D F)) h) :
    0<deriv (wedgeWidth D F) h*deriv (deriv (deriv (wedgeWidth D F))) h-
      3*(deriv (deriv (wedgeWidth D F)) h)^2 := by
  have hF : 0<F := by linarith
  have hw := wedgeWidth_pos hF hh
  have hw1 := wedgeWidth_deriv_pos hF hh
  have hk := saddleK_pos hD hF0 hF1 hhalf hh
  have hsecond := physical_curvature_identity hD hF0 hF1 hhalf hh
  have hp : 0<saddleCurvature D F h := by
    have hmul := mul_pos hchi hk
    rw [hsecond] at hmul
    exact pos_of_mul_pos_right hmul (sq_pos_of_pos hw1).le
  have hPhi' : HasDerivAt (saddleCurvature D F)
      (deriv (wedgeWidth D F) h/wedgeWidth D F h*saddleCurvature D F h*
        (RX/saddleCurvature D F h-1)) h := by
    apply hPhi.congr_deriv
    unfold wedgeRate
    field_simp [hp.ne']
    <;> ring
  have hthird := widthjet_third_identity (isOpen_admissibleEnergy D F) hh
    (analyticAt_wedgeWidth hh) hw.ne'
    (by simpa only [wedgeRate,neg_div] using hasDerivAt_saddleK hD hF0 hF1 hhalf hh) hPhi'
      (fun t ht => physical_curvature_identity hD hF0 hF1 hhalf ht)
  have hid := widthjet_rchi_eq hw1.ne' hk.ne' hsecond hthird
  have hleft : 0<(saddleCurvature D F h/saddleK D F h)*(RX/saddleCurvature D F h) :=
    mul_pos (div_pos hp hk) (div_pos hRX hp)
  rw [hid] at hleft
  have hnum := (div_pos_iff_of_pos_right (pow_pos hw1 4)).mp hleft
  exact pos_of_mul_pos_right hnum (sq_pos_of_pos hw).le

end LeanVerification.PositiveDCompletion
