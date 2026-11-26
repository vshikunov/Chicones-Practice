import LeanVerification.EnergyReparametrization
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Analytic energy coordinates preserve zero multiplicities

This module proves the analytic zero-order assertion used in Lemma 2.2
of the v9 manuscript. Its hypotheses are local analytic hypotheses on
the period and the coordinate. Analyticity of the actual Loud quadrature
is a separate obligation; it is not introduced here as an axiom.

The proof uses the analytic divided difference of the coordinate. It
therefore treats both coordinate orientations and all finite orders,
as well as a locally identically zero derivative.
-/

noncomputable section

namespace LeanVerification.AnalyticReparametrization

open Filter Set
open scoped Topology

theorem analyticAt_dslope {f : ℝ → ℝ} {s : ℝ}
    (hf : AnalyticAt ℝ f s) : AnalyticAt ℝ (dslope f s) s := by
  obtain ⟨p, hp⟩ := hf
  exact hp.has_fpower_series_dslope_fslope.analyticAt

/-- A regular analytic coordinate does not change the order of an
analytic germ, including the infinite order of a locally zero germ. -/
theorem order_comp_regular {f χ : ℝ → ℝ} {s : ℝ}
    (hf : AnalyticAt ℝ f (χ s)) (hχ : AnalyticAt ℝ χ s)
    (hregular : deriv χ s ≠ 0) :
    (hf.comp hχ).order = hf.order := by
  by_cases htop : hf.order = ⊤
  · rw [htop]
    apply (hf.comp hχ).order_eq_top_iff.mpr
    exact hχ.continuousAt.tendsto.eventually (hf.order_eq_top_iff.mp htop)
  · have hn : hf.order = (hf.order.toNat : ENat) := (ENat.coe_toNat htop).symm
    obtain ⟨g, hg, hgnz, hfg⟩ := hf.order_eq_nat_iff.mp hn
    have hb := analyticAt_dslope hχ
    have hbnz : dslope χ s s ≠ 0 := by simpa only [dslope_same] using hregular
    rw [hn]
    apply (hf.comp hχ).order_eq_nat_iff.mpr
    refine ⟨fun t => (dslope χ s t) ^ hf.order.toNat * g (χ t),
      (hb.pow _).mul (hg.comp hχ), mul_ne_zero (pow_ne_zero _ hbnz) hgnz, ?_⟩
    have he := hχ.continuousAt.tendsto.eventually hfg
    filter_upwards [he] with t ht
    have hfactor : χ t - χ s = (t - s) * dslope χ s t := by
      simpa only [smul_eq_mul] using (sub_smul_dslope χ s t).symm
    simpa only [Function.comp_apply, smul_eq_mul, hfactor, mul_pow, mul_assoc] using ht

/-- Multiplication by a nonvanishing analytic factor preserves the order. -/
theorem order_mul_nonvanishing {f g : ℝ → ℝ} {s : ℝ}
    (hf : AnalyticAt ℝ f s) (hg : AnalyticAt ℝ g s) (hg0 : g s ≠ 0) :
    (hf.mul hg).order = hf.order := by
  rw [hf.order_mul hg, hg.order_eq_zero_iff.mpr hg0, add_zero]

theorem deriv_comp_eventually {T χ : ℝ → ℝ} {s : ℝ}
    (hT : AnalyticAt ℝ T (χ s)) (hχ : AnalyticAt ℝ χ s) :
    deriv (T ∘ χ) =ᶠ[𝓝 s] fun t => deriv T (χ t) * deriv χ t := by
  have hTnear := hχ.continuousAt.tendsto.eventually hT.eventually_analyticAt
  filter_upwards [hTnear, hχ.eventually_analyticAt] with t htT htχ
  exact deriv_comp t htT.differentiableAt htχ.differentiableAt

/-- Exact preservation of the order of the period derivative. -/
theorem critical_order_preserved {T χ : ℝ → ℝ} {s : ℝ}
    (hT : AnalyticAt ℝ T (χ s)) (hχ : AnalyticAt ℝ χ s)
    (hregular : deriv χ s ≠ 0) :
    (hT.comp hχ).deriv.order = hT.deriv.order := by
  have hc := hT.deriv.comp hχ
  have hd := hc.mul hχ.deriv
  have he := deriv_comp_eventually hT hχ
  calc
    (hT.comp hχ).deriv.order = hd.order := by
      simpa using ((hT.comp hχ).deriv.order_congr he).symm
    _ = hc.order := order_mul_nonvanishing hc hχ.deriv hregular
    _ = hT.deriv.order := order_comp_regular hT.deriv hχ hregular

theorem critical_multiplicity_iff {T χ : ℝ → ℝ} {s : ℝ} {m : ℕ}
    (hT : AnalyticAt ℝ T (χ s)) (hχ : AnalyticAt ℝ χ s)
    (hregular : deriv χ s ≠ 0) :
    (hT.comp hχ).deriv.order = (m : ENat) ↔
      hT.deriv.order = (m : ENat) := by
  rw [critical_order_preserved hT hχ hregular]

theorem locally_constant_period_derivative_iff {T χ : ℝ → ℝ} {s : ℝ}
    (hT : AnalyticAt ℝ T (χ s)) (hχ : AnalyticAt ℝ χ s)
    (hregular : deriv χ s ≠ 0) :
    (∀ᶠ t in 𝓝 s, deriv (T ∘ χ) t = 0) ↔
      ∀ᶠ h in 𝓝 (χ s), deriv T h = 0 := by
  rw [← (hT.comp hχ).deriv.order_eq_top_iff, ← hT.deriv.order_eq_top_iff,
    critical_order_preserved hT hχ hregular]

theorem stationarity_iff {T χ : ℝ → ℝ} {s : ℝ}
    (hT : AnalyticAt ℝ T (χ s)) (hχ : AnalyticAt ℝ χ s)
    (hregular : deriv χ s ≠ 0) :
    deriv (T ∘ χ) s = 0 ↔ deriv T (χ s) = 0 := by
  rw [deriv_comp s hT.differentiableAt hχ.differentiableAt]
  simp only [mul_eq_zero, hregular, or_false]

/-- On an interval, a nonvanishing derivative makes the analytic energy
coordinate injective. Neither orientation is selected in the hypotheses. -/
theorem regular_coordinate_injOn {χ : ℝ → ℝ} {J : Set ℝ}
    (hJ : Convex ℝ J) (hχ : AnalyticOnNhd ℝ χ J)
    (hregular : ∀ s ∈ J, deriv χ s ≠ 0) : Set.InjOn χ J := by
  have hordered : ∀ {x y : ℝ}, x ∈ J → y ∈ J → x < y → χ x = χ y → False := by
    intro x y hx hy hxy heq
    have hsub : Icc x y ⊆ J := hJ.ordConnected.out hx hy
    obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_zero hxy
      (hχ.continuousOn.mono hsub) heq
    exact hregular c (hsub ⟨hc.1.le, hc.2.le⟩) hdc
  intro x hx y hy heq
  rcases lt_trichotomy x y with hlt | hequal | hgt
  · exact (hordered hx hy hlt heq).elim
  · exact hequal
  · exact (hordered hy hx hgt heq.symm).elim

/-- The coordinate gives a bijection between the two stationary sets,
with the target restricted to its actual image, as in Lemma 2.2. -/
theorem stationary_sets_bijective {T χ : ℝ → ℝ} {J : Set ℝ}
    (hJ : Convex ℝ J) (hχ : AnalyticOnNhd ℝ χ J)
    (hT : AnalyticOnNhd ℝ T (χ '' J))
    (hregular : ∀ s ∈ J, deriv χ s ≠ 0) :
    Set.BijOn χ {s | s ∈ J ∧ deriv (T ∘ χ) s = 0}
      {h | h ∈ χ '' J ∧ deriv T h = 0} := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have himage : χ s ∈ χ '' J := ⟨s, hs.1, rfl⟩
    exact ⟨himage, (stationarity_iff (hT (χ s) himage) (hχ s hs.1)
      (hregular s hs.1)).mp hs.2⟩
  · exact (regular_coordinate_injOn hJ hχ hregular).mono (fun _ hs => hs.1)
  · intro h hh
    obtain ⟨s, hs, rfl⟩ := hh.1
    refine ⟨s, ⟨hs, ?_⟩, rfl⟩
    exact (stationarity_iff (hT (χ s) ⟨s, hs, rfl⟩) (hχ s hs)
      (hregular s hs)).mpr hh.2

/-- The stationary curvature formula needs only local analytic data. -/
theorem stationary_curvature {T χ : ℝ → ℝ} {s : ℝ}
    (hT : AnalyticAt ℝ T (χ s)) (hχ : AnalyticAt ℝ χ s)
    (hcritical : deriv T (χ s) = 0) :
    deriv (deriv (T ∘ χ)) s =
      (deriv χ s) ^ 2 * deriv (deriv T) (χ s) := by
  have hd := (hT.deriv.differentiableAt.hasDerivAt.comp s
    hχ.differentiableAt.hasDerivAt).mul hχ.deriv.differentiableAt.hasDerivAt
  rw [(deriv_comp_eventually hT hχ).deriv_eq]
  change deriv (fun y => (deriv T ∘ χ) y * deriv χ y) s = _
  rw [hd.deriv]
  simp only [Function.comp_apply, hcritical, zero_mul, add_zero]
  ring

theorem positive_stationary_curvature_preserved {T χ : ℝ → ℝ} {s : ℝ}
    (hT : AnalyticAt ℝ T (χ s)) (hχ : AnalyticAt ℝ χ s)
    (hregular : deriv χ s ≠ 0) (hcritical : deriv T (χ s) = 0)
    (hpositive : 0 < deriv (deriv T) (χ s)) :
    0 < deriv (deriv (T ∘ χ)) s := by
  rw [stationary_curvature hT hχ hcritical]
  exact mul_pos (sq_pos_of_ne_zero hregular) hpositive

end LeanVerification.AnalyticReparametrization
