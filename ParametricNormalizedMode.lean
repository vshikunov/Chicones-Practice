import LeanVerification.ParametricSpatialJet
import LeanVerification.CriticalEnergy

/-! Joint parameter regularity of the actual normalized variation formula. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace LeanVerification.ParametricNormalizedMode

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coefficient (W φ : E × ℝ → ℝ) (e : E → ℝ) (p : E × ℝ) : ℝ :=
  CriticalEnergy.coefficientH (fun x => W (p.1,x)) (fun x => φ (p.1,x)) (e p.1) p.2

def mode (W φ Y : E × ℝ → ℝ) (e : E → ℝ) (p : E × ℝ) : ℝ :=
  (φ p * ParametricSpatialJet.jet Y 1 p - ParametricSpatialJet.jet φ 1 p * Y p) *
    coefficient W φ e p ^ (-(1 : ℝ)/3)

theorem analyticAt_coefficient {W φ : E × ℝ → ℝ} {e : E → ℝ} {p : E × ℝ}
    (hW : AnalyticAt ℝ W p) (hφ : AnalyticAt ℝ φ p) (he : AnalyticAt ℝ e p.1) :
    AnalyticAt ℝ (coefficient W φ e) p := by
  have hW₁ := ParametricSpatialJet.analyticAt_jet hW 1
  have hW₂ := ParametricSpatialJet.analyticAt_jet hW 2
  have hφ₁ := ParametricSpatialJet.analyticAt_jet hφ 1
  have hφ₂ := ParametricSpatialJet.analyticAt_jet hφ 2
  have he' := he.comp_of_eq (f := fun q : E × ℝ => q.1) analyticAt_fst rfl
  convert ((hφ.mul hW₂).sub (hφ₁.mul hW₁)).add
    (((analyticAt_const (v := (2 : ℝ))).mul (he'.sub hW)).mul hφ₂) using 1
  funext q
  simp only [coefficient,CriticalEnergy.coefficientH,CriticalEnergy.gap,CriticalEnergy.jet,
    ParametricSpatialJet.jet,iteratedDeriv_eq_iterate,
    Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Function.comp_apply,Prod.mk.eta]

theorem analyticAt_mode {W φ Y : E × ℝ → ℝ} {e : E → ℝ} {p : E × ℝ}
    (hW : AnalyticAt ℝ W p) (hφ : AnalyticAt ℝ φ p) (hY : AnalyticAt ℝ Y p)
    (he : AnalyticAt ℝ e p.1) (hH : 0 < coefficient W φ e p) :
    AnalyticAt ℝ (mode W φ Y e) p := by
  have hHa := analyticAt_coefficient hW hφ he
  have hp : AnalyticAt ℝ (fun q => coefficient W φ e q ^ (-(1 : ℝ)/3)) p :=
    (Real.contDiffAt_rpow_const_of_ne (p := -(1 : ℝ)/3) (n := ω) hH.ne').analyticAt.comp_of_eq hHa rfl
  exact ((hφ.mul (ParametricSpatialJet.analyticAt_jet hY 1)).sub
    ((ParametricSpatialJet.analyticAt_jet hφ 1).mul hY)).mul hp

end LeanVerification.ParametricNormalizedMode
