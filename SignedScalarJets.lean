import LeanVerification.PositiveDCompletion.SignedModelAlgebra
import LeanVerification.ReflectedWedgeCompletion.DiagonalJet00
import LeanVerification.ReflectedWedgeCompletion.DiagonalJet01
import LeanVerification.ReflectedWedgeCompletion.DiagonalJet02
import LeanVerification.ReflectedWedgeCompletion.DiagonalJet03
import LeanVerification.ReflectedWedgeCompletion.DiagonalJet04
import LeanVerification.ReflectedWedgeCompletion.DiagonalJet05

noncomputable section
open Filter
open scoped Topology
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

theorem modelAlpha1_hasDerivAt_diagonal {ff rr : ℝ → ℝ} {a h scale : ℝ}
    (hc : SignedRegular a (ff h) (rr h))
    (hCone : ∀ᶠ x in 𝓝 h, SignedRegular a (ff x) (rr x))
    (hff : HasDerivAt ff (scale*diagonalTransportF a (ff h) (rr h)) h)
    (hrr : HasDerivAt rr (scale*diagonalTransportRho a (ff h) (rr h)) h) :
    HasDerivAt (fun x => modelAlpha1 a (ff x) (rr x)) (scale*jetDAlpha1 a (ff h) (rr h)) h := by
  have hd := jetAlpha1_hasDerivAt hc.a_ne
    hc.j_ne hc.g_ne
    hc.f_a_ne hc.f_one_ne
    hc.rho_one_ne hc.A_ne hff hrr
  have he : (fun x => modelAlpha1 a (ff x) (rr x)) =ᶠ[𝓝 h]
      (fun x => jetAlpha1 a (ff x) (rr x)) := by
    filter_upwards [hCone] with x hx
    exact hx.modelAlpha1_eq_jet
  exact hd.congr_of_eventuallyEq he

theorem modelAlpha2_hasDerivAt_diagonal {ff rr : ℝ → ℝ} {a h scale : ℝ}
    (hc : SignedRegular a (ff h) (rr h))
    (hCone : ∀ᶠ x in 𝓝 h, SignedRegular a (ff x) (rr x))
    (hff : HasDerivAt ff (scale*diagonalTransportF a (ff h) (rr h)) h)
    (hrr : HasDerivAt rr (scale*diagonalTransportRho a (ff h) (rr h)) h) :
    HasDerivAt (fun x => modelAlpha2 a (ff x) (rr x)) (scale*jetDAlpha2 a (ff h) (rr h)) h := by
  have hd := jetAlpha2_hasDerivAt hc.a_ne
    hc.j_ne hc.g_ne
    hc.f_a_ne hc.f_one_ne
    hc.rho_one_ne hc.A_ne hff hrr
  have he : (fun x => modelAlpha2 a (ff x) (rr x)) =ᶠ[𝓝 h]
      (fun x => jetAlpha2 a (ff x) (rr x)) := by
    filter_upwards [hCone] with x hx
    exact hx.modelAlpha2_eq_jet
  exact hd.congr_of_eventuallyEq he

theorem modelAlpha3_hasDerivAt_diagonal {ff rr : ℝ → ℝ} {a h scale : ℝ}
    (hc : SignedRegular a (ff h) (rr h))
    (hCone : ∀ᶠ x in 𝓝 h, SignedRegular a (ff x) (rr x))
    (hff : HasDerivAt ff (scale*diagonalTransportF a (ff h) (rr h)) h)
    (hrr : HasDerivAt rr (scale*diagonalTransportRho a (ff h) (rr h)) h) :
    HasDerivAt (fun x => modelAlpha3 a (ff x) (rr x)) (scale*jetDAlpha3 a (ff h) (rr h)) h := by
  have hd := jetAlpha3_hasDerivAt hc.a_ne
    hc.j_ne hc.g_ne
    hc.f_a_ne hc.f_one_ne
    hc.rho_one_ne hc.A_ne hff hrr
  have he : (fun x => modelAlpha3 a (ff x) (rr x)) =ᶠ[𝓝 h]
      (fun x => jetAlpha3 a (ff x) (rr x)) := by
    filter_upwards [hCone] with x hx
    exact hx.modelAlpha3_eq_jet
  exact hd.congr_of_eventuallyEq he

theorem modelAlpha4_hasDerivAt_diagonal {ff rr : ℝ → ℝ} {a h scale : ℝ}
    (hc : SignedRegular a (ff h) (rr h))
    (hCone : ∀ᶠ x in 𝓝 h, SignedRegular a (ff x) (rr x))
    (hff : HasDerivAt ff (scale*diagonalTransportF a (ff h) (rr h)) h)
    (hrr : HasDerivAt rr (scale*diagonalTransportRho a (ff h) (rr h)) h) :
    HasDerivAt (fun x => modelAlpha4 a (ff x) (rr x)) (scale*jetDAlpha4 a (ff h) (rr h)) h := by
  have hd := jetAlpha4_hasDerivAt hc.a_ne
    hc.j_ne hc.g_ne
    hc.f_a_ne hc.f_one_ne
    hc.rho_one_ne hc.A_ne hff hrr
  have he : (fun x => modelAlpha4 a (ff x) (rr x)) =ᶠ[𝓝 h]
      (fun x => jetAlpha4 a (ff x) (rr x)) := by
    filter_upwards [hCone] with x hx
    exact hx.modelAlpha4_eq_jet
  exact hd.congr_of_eventuallyEq he

theorem modelEll_hasDerivAt_diagonal {ff rr : ℝ → ℝ} {a h scale : ℝ}
    (hc : SignedRegular a (ff h) (rr h))
    (hCone : ∀ᶠ x in 𝓝 h, SignedRegular a (ff x) (rr x))
    (hff : HasDerivAt ff (scale*diagonalTransportF a (ff h) (rr h)) h)
    (hrr : HasDerivAt rr (scale*diagonalTransportRho a (ff h) (rr h)) h) :
    HasDerivAt (fun x => modelEll a (ff x) (rr x)) (-scale*modelPoleFlow a (ff h) (rr h)) h := by
  have hd := jetEll_hasDerivAt hc.a_ne
    hc.j_ne hc.g_ne
    hc.f_a_ne hc.f_one_ne
    hc.rho_one_ne hc.A_ne hff hrr
  rw [←hc.modelPoleFlow_eq_jet] at hd
  have he : (fun x => modelEll a (ff x) (rr x)) =ᶠ[𝓝 h]
      (fun x => jetEll a (ff x) (rr x)) := by
    filter_upwards [hCone] with x hx
    exact hx.modelEll_eq_jet
  exact hd.congr_of_eventuallyEq he

theorem modelFZero_hasDerivAt_diagonal {ff rr : ℝ → ℝ} {a h scale : ℝ}
    (hc : SignedRegular a (ff h) (rr h))
    (hCone : ∀ᶠ x in 𝓝 h, SignedRegular a (ff x) (rr x))
    (hff : HasDerivAt ff (scale*diagonalTransportF a (ff h) (rr h)) h)
    (hrr : HasDerivAt rr (scale*diagonalTransportRho a (ff h) (rr h)) h) :
    HasDerivAt (fun x => modelFZero a (ff x) (rr x)) (scale*modelFZero a (ff h) (rr h)*(modelRZero a (ff h) (rr h)-1)) h := by
  have hd := jetFZero_hasDerivAt hc.a_ne
    hc.j_ne hc.g_ne
    hc.f_a_ne hc.f_one_ne
    hc.rho_one_ne hc.A_ne hff hrr
  rw [←hc.modelFZero_eq_jet,←hc.modelRZero_eq_jet] at hd
  have he : (fun x => modelFZero a (ff x) (rr x)) =ᶠ[𝓝 h]
      (fun x => jetFZero a (ff x) (rr x)) := by
    filter_upwards [hCone] with x hx
    exact hx.modelFZero_eq_jet
  exact hd.congr_of_eventuallyEq he

end LeanVerification.PositiveDCompletion
