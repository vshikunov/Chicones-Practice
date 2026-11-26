import LeanVerification.PositiveDCompletion.PhysicalModel
import LeanVerification.ReflectedWedgeCompletion.RationalModel

noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.PositiveDCompletion
open Loud ReflectedCompletion ReflectedWedgeCompletion

/-- Exactly the denominator exclusions needed by the already checked rational jets. -/
structure SignedRegular (a f rho : ℝ) : Prop where
  a_ne : a≠0
  j_ne : 1+f≠0
  g_ne : modelG a rho≠0
  f_a_ne : f-a≠0
  f_one_ne : 1-f≠0
  rho_one_ne : 1-rho≠0
  A_ne : modelA a f rho≠0

theorem actual_signed_regular {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    SignedRegular (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) := by
  obtain ⟨ha,hau,hd,hes⟩ := positiveD_parameter_bounds hD hF0 hF1
  have hF : 0<F := by linarith
  have ha1 := lowerPhysicalA_ne_one hF hhalf
  have hq := wedgeLogSecant_pos hF hh
  obtain ⟨han,hj,hw,hA,hN⟩ := actual_signed_denominators hD hF0 hF1 hhalf hh
  have hg := secant_g_ne_zero ha ha1 hq
  refine ⟨han,hj,hg,?_,saddleF_ne_one ha ha1 hF hh,?_,hA⟩
  · rcases lt_or_gt_of_ne ha1 with hl|hu
    · have hf := (secantF_bounds ha hl hq).1
      change lowerPhysicalA F<wedgeF D F h at hf
      linarith
    · have hf := (secant_lower_bounds hu hq).2.1
      change wedgeF D F h<lowerPhysicalA F at hf
      linarith
  · rcases lt_or_gt_of_ne ha1 with hl|hu
    · have hr := (secantRho_bounds ha hl hq).2
      change wedgeRho D F h<1 at hr
      linarith
    · have hr := (secant_lower_bounds hu hq).2.2
      change 1<wedgeRho D F h at hr
      linarith

end LeanVerification.PositiveDCompletion
