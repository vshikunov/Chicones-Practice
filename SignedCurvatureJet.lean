import LeanVerification.PositiveDCompletion.SignedScalarJets
import LeanVerification.PositiveDCompletion.SignedSourceCoefficients
import LeanVerification.ReflectedWedgeCompletion.SourceDerivative

noncomputable section
open Filter
open scoped Topology
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 16000000
set_option maxRecDepth 50000

theorem modelF_hasDerivAt_full {ff rr ww : ℝ → ℝ} {a h lam : ℝ}
    (hc : SignedRegular a (ff h) (rr h))
    (hCone : ∀ᶠ x in 𝓝 h, SignedRegular a (ff x) (rr x))
    (hW : 1+ww h≠0) (hN : transportN a (ff h) (rr h) (ww h)≠0)
    (hPsi : modelPsi a (ff h) (rr h) (ww h)≠0)
    (hff : HasDerivAt ff (lam*transportF a (ff h) (rr h) (ww h)) h)
    (hrr : HasDerivAt rr (lam*transportRho a (ff h) (rr h) (ww h)) h)
    (hww : HasDerivAt ww (lam*transportOmega a (ff h) (rr h) (ww h)) h) :
    HasDerivAt (fun x => modelF a (ff x) (rr x) (ww x))
      (lam*modelF a (ff h) (rr h) (ww h)*(modelR a (ff h) (rr h) (ww h)-1)) h := by
  have hL := hc.modelL_ne hN
  have hff' : HasDerivAt ff
      ((lam*modelLambda a (ff h) (rr h) (ww h))*diagonalTransportF a (ff h) (rr h)) h := by
    convert hff using 1
    rw [←hc.modelLambda_transportF hN]
    ring
  have hrr' : HasDerivAt rr
      ((lam*modelLambda a (ff h) (rr h) (ww h))*diagonalTransportRho a (ff h) (rr h)) h := by
    convert hrr using 1
    rw [←hc.modelLambda_transportRho hN]
    ring
  have hw' : HasDerivAt ww
      (-lam*2*modelM a (ff h) (rr h)*ww h*(1+ww h)/modelL a (ff h) (rr h) (ww h)) h := by
    convert hww using 1
    rw [←hc.modelOmega_transport hN]
    ring
  have ha₁ := modelAlpha1_hasDerivAt_diagonal hc hCone hff' hrr'
  have ha₂ := modelAlpha2_hasDerivAt_diagonal hc hCone hff' hrr'
  have ha₃ := modelAlpha3_hasDerivAt_diagonal hc hCone hff' hrr'
  have ha₄ := modelAlpha4_hasDerivAt_diagonal hc hCone hff' hrr'
  have hb := modelEll_hasDerivAt_diagonal hc hCone hff' hrr'
  have hp := modelFZero_hasDerivAt_diagonal hc hCone hff' hrr'
  have hps := compactPsi_hasDerivAt_flow hL
    (show HasDerivAt (fun x => modelAlpha1 a (ff x) (rr x))
      (lam*(1+modelSigma (ff h)*ww h)/(1+modelEll a (ff h) (rr h)*ww h)*jetDAlpha1 a (ff h) (rr h)) h by
      convert ha₁ using 1;unfold modelLambda modelL;ring)
    (show HasDerivAt (fun x => modelAlpha2 a (ff x) (rr x))
      (lam*(1+modelSigma (ff h)*ww h)/(1+modelEll a (ff h) (rr h)*ww h)*jetDAlpha2 a (ff h) (rr h)) h by
      convert ha₂ using 1;unfold modelLambda modelL;ring)
    (show HasDerivAt (fun x => modelAlpha3 a (ff x) (rr x))
      (lam*(1+modelSigma (ff h)*ww h)/(1+modelEll a (ff h) (rr h)*ww h)*jetDAlpha3 a (ff h) (rr h)) h by
      convert ha₃ using 1;unfold modelLambda modelL;ring)
    (show HasDerivAt (fun x => modelAlpha4 a (ff x) (rr x))
      (lam*(1+modelSigma (ff h)*ww h)/(1+modelEll a (ff h) (rr h)*ww h)*jetDAlpha4 a (ff h) (rr h)) h by
      convert ha₄ using 1;unfold modelLambda modelL;ring) hw'
  rw [←hc.sourceCoefficient1_identity,←hc.sourceCoefficient2_identity,
    ←hc.sourceCoefficient3_identity,←hc.sourceCoefficient4_identity,
    ←hc.sourceCoefficient5_identity] at hps
  have hb' : HasDerivAt (fun x => modelEll a (ff x) (rr x))
      (-lam*((1+modelSigma (ff h)*ww h)/(1+modelEll a (ff h) (rr h)*ww h))*modelPoleFlow a (ff h) (rr h)) h := by
    apply hb.congr_deriv
    dsimp only [modelLambda,modelL]
    ring
  have hd := complete_curvature_source_derivative
    (p := fun x => modelFZero a (ff x) (rr x))
    (b := fun x => modelEll a (ff x) (rr x)) (w := ww)
    (A₁ := fun x => modelAlpha1 a (ff x) (rr x))
    (A₂ := fun x => modelAlpha2 a (ff x) (rr x))
    (A₃ := fun x => modelAlpha3 a (ff x) (rr x))
    (A₄ := fun x => modelAlpha4 a (ff x) (rr x))
    (lam := lam) (M := modelM a (ff h) (rr h)) (sigma := modelSigma (ff h))
    (t := modelPoleFlow a (ff h) (rr h)) (R₀ := modelRZero a (ff h) (rr h))
    (v₁ := modelV1 a (ff h) (rr h)) (v₂ := modelV2 a (ff h) (rr h))
    (v₃ := modelV3 a (ff h) (rr h)) (v₄ := modelV4 a (ff h) (rr h))
    (v₅ := modelV5 a (ff h) (rr h)) hL
    hW hPsi
    hp hb' hw' hps
  apply hd.congr_deriv
  dsimp only [modelF,modelPsi,modelL,modelR,modelLambda,modelSource]
  ring

end LeanVerification.PositiveDCompletion
