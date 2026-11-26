import LeanVerification.AnalyticTwoPartials

/-! Ordinary spatial jets of a jointly analytic family, with arbitrary real
normed parameters. All jet regularity follows from the analytic family. -/
noncomputable section
open Filter
open scoped Topology
namespace LeanVerification.ParametricSpatialJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def jet (f : E × ℝ → ℝ) (n : ℕ) (p : E × ℝ) : ℝ :=
  iteratedDeriv n (fun x => f (p.1,x)) p.2

theorem analyticAt_jet {f : E × ℝ → ℝ} {p : E × ℝ}
    (hf : AnalyticAt ℝ f p) (n : ℕ) : AnalyticAt ℝ (jet f n) p := by
  induction n generalizing p with
  | zero => simpa only [jet,iteratedDeriv_zero,Prod.mk.eta] using hf
  | succ n ih =>
    have hj := ih hf
    let ev : ((E × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ ((0,1) : E × ℝ)
    have hd : AnalyticAt ℝ (fun q => fderiv ℝ (jet f n) q (0,1)) p :=
      (ev.analyticAt _).comp hj.fderiv
    apply hd.congr
    filter_upwards [hf.eventually_analyticAt] with q hq
    have hv : HasDerivAt (fun x : ℝ => (q.1,x)) (0,1) q.2 :=
      (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
    simpa only [jet,iteratedDeriv_succ] using
      ((ih hq).differentiableAt.hasFDerivAt.comp_hasDerivAt q.2 hv).deriv.symm

theorem jet_one_eq_deriv (f : E × ℝ → ℝ) (p : E × ℝ) :
    jet f 1 p = deriv (fun x => f (p.1,x)) p.2 := by simp [jet]

end LeanVerification.ParametricSpatialJet
