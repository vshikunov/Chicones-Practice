import LeanVerification.AnalyticReparametrization
import LeanVerification.Loud.MorseInverse
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Analysis.Convex.Topology

/-!
# Actual analytic inverses and preservation of local extrema

A regular analytic coordinate on a convex open real set has the selected
inverse `invFunOn` on its actual image. The image is open and the inverse
is analytic there. Local minima and maxima, including degenerate extrema,
are preserved in both directions without choosing a coordinate orientation.

These are general coordinate theorems. They do not establish analyticity
of the actual Loud period integral.
-/

noncomputable section

namespace LeanVerification.RegularEnergyCoordinate

open Set Filter
open scoped Topology

def coordinateInverse (χ : ℝ → ℝ) (J : Set ℝ) : ℝ → ℝ :=
  Function.invFunOn χ J

theorem coordinateInverse_mem {χ : ℝ → ℝ} {J : Set ℝ} {h : ℝ}
    (hh : h ∈ χ '' J) : coordinateInverse χ J h ∈ J :=
  Function.invFunOn_mem hh

theorem coordinate_coordinateInverse {χ : ℝ → ℝ} {J : Set ℝ} {h : ℝ}
    (hh : h ∈ χ '' J) : χ (coordinateInverse χ J h) = h :=
  Function.invFunOn_eq hh

theorem coordinateInverse_coordinate {χ : ℝ → ℝ} {J : Set ℝ}
    (hJ : Convex ℝ J) (hχ : AnalyticOnNhd ℝ χ J)
    (hregular : ∀ s ∈ J, deriv χ s ≠ 0) {s : ℝ} (hs : s ∈ J) :
    coordinateInverse χ J (χ s) = s :=
  (AnalyticReparametrization.regular_coordinate_injOn hJ hχ hregular).leftInvOn_invFunOn hs

theorem coordinate_bijOn {χ : ℝ → ℝ} {J : Set ℝ}
    (hJ : Convex ℝ J) (hχ : AnalyticOnNhd ℝ χ J)
    (hregular : ∀ s ∈ J, deriv χ s ≠ 0) : Set.BijOn χ J (χ '' J) := by
  refine ⟨fun s hs => ⟨s, hs, rfl⟩,
    AnalyticReparametrization.regular_coordinate_injOn hJ hχ hregular, ?_⟩
  rintro h ⟨s, hs, rfl⟩
  exact ⟨s, hs, rfl⟩

theorem isOpen_coordinate_image {χ : ℝ → ℝ} {J : Set ℝ}
    (hopen : IsOpen J) (hχ : AnalyticOnNhd ℝ χ J)
    (hregular : ∀ s ∈ J, deriv χ s ≠ 0) : IsOpen (χ '' J) := by
  rw [isOpen_iff_mem_nhds]
  rintro h ⟨s, hs, rfl⟩
  have hd : HasStrictDerivAt χ (deriv χ s) s :=
    (hχ s hs).hasStrictFDerivAt.hasStrictDerivAt
  rw [← hd.map_nhds_eq (hregular s hs)]
  exact Filter.image_mem_map (hopen.mem_nhds hs)

theorem convex_coordinate_image {χ : ℝ → ℝ} {J : Set ℝ}
    (hJ : Convex ℝ J) (hχ : AnalyticOnNhd ℝ χ J) : Convex ℝ (χ '' J) :=
  (hJ.isPreconnected.image χ hχ.continuousOn).convex

theorem analyticAt_coordinateInverse {χ : ℝ → ℝ} {J : Set ℝ}
    (hJ : Convex ℝ J) (hopen : IsOpen J) (hχ : AnalyticOnNhd ℝ χ J)
    (hregular : ∀ s ∈ J, deriv χ s ≠ 0) {h : ℝ} (hh : h ∈ χ '' J) :
    AnalyticAt ℝ (coordinateInverse χ J) h := by
  let s := coordinateInverse χ J h
  have hs : s ∈ J := coordinateInverse_mem hh
  have hleft : ∀ᶠ t in 𝓝 s, coordinateInverse χ J (χ t) = t := by
    filter_upwards [hopen.mem_nhds hs] with t ht
    exact coordinateInverse_coordinate hJ hχ hregular ht
  have hd : HasStrictDerivAt χ (deriv χ s) s :=
    (hχ s hs).hasStrictFDerivAt.hasStrictDerivAt
  have hi := Loud.analyticAt_of_local_left_inverse (hχ s hs) hd (hregular s hs) hleft
  simpa only [s, coordinate_coordinateInverse hh] using hi

theorem analyticOnNhd_coordinateInverse {χ : ℝ → ℝ} {J : Set ℝ}
    (hJ : Convex ℝ J) (hopen : IsOpen J) (hχ : AnalyticOnNhd ℝ χ J)
    (hregular : ∀ s ∈ J, deriv χ s ≠ 0) :
    AnalyticOnNhd ℝ (coordinateInverse χ J) (χ '' J) :=
  fun _ hh => analyticAt_coordinateInverse hJ hopen hχ hregular hh

theorem hasDerivAt_coordinateInverse {χ : ℝ → ℝ} {J : Set ℝ}
    (hJ : Convex ℝ J) (hopen : IsOpen J) (hχ : AnalyticOnNhd ℝ χ J)
    (hregular : ∀ s ∈ J, deriv χ s ≠ 0) {h : ℝ} (hh : h ∈ χ '' J) :
    HasDerivAt (coordinateInverse χ J)
      (deriv χ (coordinateInverse χ J h))⁻¹ h := by
  let s := coordinateInverse χ J h
  have hs : s ∈ J := coordinateInverse_mem hh
  have hleft : ∀ᶠ t in 𝓝 s, coordinateInverse χ J (χ t) = t := by
    filter_upwards [hopen.mem_nhds hs] with t ht
    exact coordinateInverse_coordinate hJ hχ hregular ht
  have hd : HasStrictDerivAt χ (deriv χ s) s :=
    (hχ s hs).hasStrictFDerivAt.hasStrictDerivAt
  have hi := hd.to_local_left_inverse (hregular s hs) hleft
  simpa only [s, coordinate_coordinateInverse hh] using hi.hasDerivAt

theorem coordinateInverse_deriv_ne_zero {χ : ℝ → ℝ} {J : Set ℝ}
    (hJ : Convex ℝ J) (hopen : IsOpen J) (hχ : AnalyticOnNhd ℝ χ J)
    (hregular : ∀ s ∈ J, deriv χ s ≠ 0) {h : ℝ} (hh : h ∈ χ '' J) :
    deriv (coordinateInverse χ J) h ≠ 0 := by
  rw [(hasDerivAt_coordinateInverse hJ hopen hχ hregular hh).deriv]
  exact inv_ne_zero (hregular _ (coordinateInverse_mem hh))

/-- The constructed inverse is a genuine two-sided analytic inverse on
the stated open domains, rather than an assumed inverse function. -/
theorem regular_coordinate_has_analytic_inverse {χ : ℝ → ℝ} {J : Set ℝ}
    (hJ : Convex ℝ J) (hopen : IsOpen J) (hχ : AnalyticOnNhd ℝ χ J)
    (hregular : ∀ s ∈ J, deriv χ s ≠ 0) :
    IsOpen (χ '' J) ∧
      Set.BijOn χ J (χ '' J) ∧
      Set.MapsTo (coordinateInverse χ J) (χ '' J) J ∧
      Set.LeftInvOn (coordinateInverse χ J) χ J ∧
      Set.RightInvOn (coordinateInverse χ J) χ (χ '' J) ∧
      AnalyticOnNhd ℝ (coordinateInverse χ J) (χ '' J) := by
  exact ⟨isOpen_coordinate_image hopen hχ hregular,
    coordinate_bijOn hJ hχ hregular, fun _ hh => coordinateInverse_mem hh,
    fun _ hs => coordinateInverse_coordinate hJ hχ hregular hs,
    fun _ hh => coordinate_coordinateInverse hh,
    analyticOnNhd_coordinateInverse hJ hopen hχ hregular⟩

/-- Local-minimum type is preserved for arbitrary objective functions;
no derivative, nondegeneracy, or orientation assumption on that objective is needed. -/
theorem isLocalMin_comp_iff {T χ : ℝ → ℝ} {s : ℝ}
    (hχ : AnalyticAt ℝ χ s) (hregular : deriv χ s ≠ 0) :
    IsLocalMin (T ∘ χ) s ↔ IsLocalMin T (χ s) := by
  have hd : HasStrictDerivAt χ (deriv χ s) s := hχ.hasStrictFDerivAt.hasStrictDerivAt
  change (∀ᶠ t in 𝓝 s, T (χ s) ≤ T (χ t)) ↔
    ∀ᶠ h in 𝓝 (χ s), T (χ s) ≤ T h
  rw [← hd.map_nhds_eq hregular]
  rfl

/-- The same two-sided assertion holds for local maxima, including
degenerate extrema and locally constant functions. -/
theorem isLocalMax_comp_iff {T χ : ℝ → ℝ} {s : ℝ}
    (hχ : AnalyticAt ℝ χ s) (hregular : deriv χ s ≠ 0) :
    IsLocalMax (T ∘ χ) s ↔ IsLocalMax T (χ s) := by
  have hd : HasStrictDerivAt χ (deriv χ s) s := hχ.hasStrictFDerivAt.hasStrictDerivAt
  change (∀ᶠ t in 𝓝 s, T (χ t) ≤ T (χ s)) ↔
    ∀ᶠ h in 𝓝 (χ s), T h ≤ T (χ s)
  rw [← hd.map_nhds_eq hregular]
  rfl

/-- A nonzero constant clock factor preserves every analytic zero order
of the period derivative, including its locally zero alternative. -/
theorem critical_order_mul_const {T : ℝ → ℝ} {s c : ℝ}
    (hT : AnalyticAt ℝ T s) (hc : c ≠ 0) :
    (hT.mul (analyticAt_const (v := c))).deriv.order = hT.deriv.order := by
  have hd : AnalyticAt ℝ (fun t => deriv T t * c) s := hT.deriv.mul analyticAt_const
  have heq : deriv (fun t => T t * c) =ᶠ[𝓝 s] (fun t => deriv T t * c) := by
    filter_upwards [hT.eventually_analyticAt] with t ht
    exact (ht.differentiableAt.hasDerivAt.mul_const c).deriv
  calc
    (hT.mul (analyticAt_const (v := c))).deriv.order = hd.order := by
      simpa using ((hT.mul (analyticAt_const (v := c))).deriv.order_congr heq).symm
    _ = hT.deriv.order :=
      AnalyticReparametrization.order_mul_nonvanishing hT.deriv analyticAt_const hc

theorem isLocalMin_mul_pos_const_iff {T : ℝ → ℝ} {s c : ℝ} (hc : 0 < c) :
    IsLocalMin (fun t => T t * c) s ↔ IsLocalMin T s := by
  constructor
  · intro hmin
    change ∀ᶠ t in 𝓝 s, T s ≤ T t
    filter_upwards [hmin] with t ht
    exact le_of_mul_le_mul_right ht hc
  · intro hmin
    change ∀ᶠ t in 𝓝 s, T s * c ≤ T t * c
    filter_upwards [hmin] with t ht
    exact mul_le_mul_of_nonneg_right ht hc.le

theorem isLocalMax_mul_pos_const_iff {T : ℝ → ℝ} {s c : ℝ} (hc : 0 < c) :
    IsLocalMax (fun t => T t * c) s ↔ IsLocalMax T s := by
  constructor
  · intro hmax
    change ∀ᶠ t in 𝓝 s, T t ≤ T s
    filter_upwards [hmax] with t ht
    exact le_of_mul_le_mul_right ht hc
  · intro hmax
    change ∀ᶠ t in 𝓝 s, T t * c ≤ T s * c
    filter_upwards [hmax] with t ht
    exact mul_le_mul_of_nonneg_right ht hc.le

end LeanVerification.RegularEnergyCoordinate
