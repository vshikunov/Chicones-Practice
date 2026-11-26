import LeanVerification.Loud.PhysicalCriticalMode

/-!
# Normalization of a regular analytic one-turn variation

The mode equation follows locally from the actual first variational
equation. Stationarity is unnecessary for this local elimination.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace LeanVerification.AnalyticVariationMode

set_option maxHeartbeats 1000000

theorem sturm_of_analytic_variation {W φ Y : ℝ → ℝ} {L x : ℝ}
    (hW : AnalyticAt ℝ W x) (hφ : AnalyticAt ℝ φ x) (hY : AnalyticAt ℝ Y x)
    (hVpos : 0 < L - W x) (hφ0 : φ x ≠ 0)
    (hHpos : 0 < CriticalEnergy.coefficientH W φ L x)
    (heq : ∀ᶠ z in 𝓝 x, 2 * (L - W z) * deriv Y z + deriv W z * Y z = 1) :
    let H := CriticalEnergy.coefficientH W φ L
    let U := CriticalMode.mode (CriticalMode.bracket φ (deriv φ) Y (deriv Y)) H
    let p := CriticalMode.weight (fun z => L - W z) φ H
    HasDerivAt (fun z => p z * deriv U z)
      (-p x * CriticalEnergy.coefficientQ W φ L x * U x) x := by
  let V : ℝ → ℝ := fun z => L - W z
  let H := CriticalEnergy.coefficientH W φ L
  let R := CriticalMode.bracket φ (deriv φ) Y (deriv Y)
  let U := CriticalMode.mode R H
  let s : Set ℝ := {z | AnalyticAt ℝ W z ∧ AnalyticAt ℝ φ z ∧ AnalyticAt ℝ Y z ∧
    ∀ᶠ u in 𝓝 z, 2 * V u * deriv Y u + deriv W u * Y u = 1}
  have hs : IsOpen s := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    filter_upwards [hz.1.eventually_analyticAt, hz.2.1.eventually_analyticAt,
      hz.2.2.1.eventually_analyticAt, hz.2.2.2.eventually_nhds] with u huW huφ huY hue
    exact ⟨huW, huφ, huY, hue⟩
  have hx : x ∈ s := ⟨hW, hφ, hY, heq⟩
  have hfirst : ∀ z ∈ s, 2 * V z * deriv Y z + deriv W z * Y z = 1 :=
    fun _ hz => hz.2.2.2.self_of_nhds
  have hVd : ∀ z ∈ s, HasDerivAt V (-deriv W z) z :=
    fun _ hz => hz.1.differentiableAt.hasDerivAt.const_sub _
  have hsecond : ∀ z ∈ s,
      2 * V z * deriv (deriv Y) z - deriv W z * deriv Y z + deriv (deriv W) z * Y z = 0 := by
    intro z hz
    exact CriticalMode.variation_second_equation hs hz (hVd z hz)
      hz.1.deriv.differentiableAt.hasDerivAt hz.2.2.1.differentiableAt.hasDerivAt
      hz.2.2.1.deriv.differentiableAt.hasDerivAt hfirst
  have hRa : ∀ z ∈ s, AnalyticAt ℝ R z := fun _ hz =>
    (hz.2.1.mul hz.2.2.1.deriv).sub (hz.2.1.deriv.mul hz.2.2.1)
  have hHa : ∀ z ∈ s, AnalyticAt ℝ H z := fun _ hz =>
    Loud.analyticAt_criticalAuxiliary hz.1 hz.2.1
  have hfirstR : ∀ z ∈ s, 2 * V z * deriv R z = deriv W z * R z - H z * Y z := by
    intro z hz
    exact CriticalMode.bracket_first_equation hz.2.1.differentiableAt.hasDerivAt
      hz.2.1.deriv.differentiableAt.hasDerivAt hz.2.2.1.differentiableAt.hasDerivAt
      hz.2.2.1.deriv.differentiableAt.hasDerivAt (hsecond z hz)
  have hsecondR : 2 * V x * deriv (deriv R) x - 3 * deriv W x * deriv R x =
      deriv (deriv W) x * R x - deriv H x * Y x - H x * deriv Y x :=
    CriticalMode.bracket_second_equation hs hx (hVd x hx) hW.deriv.differentiableAt.hasDerivAt
      (hHa x hx).differentiableAt.hasDerivAt hY.differentiableAt.hasDerivAt
      (hRa x hx).differentiableAt.hasDerivAt (hRa x hx).deriv.differentiableAt.hasDerivAt hfirstR
  have hel := CriticalMode.bracket_elimination hVpos.ne' hφ0 hHpos.ne'
    (hfirstR x hx) hsecondR (rfl : R x = φ x * deriv Y x - deriv φ x * Y x)
    (rfl : H x = φ x * deriv (deriv W) x - deriv φ x * deriv W x + 2 * V x * deriv (deriv φ) x)
  have hd := CriticalMode.normalized_mode_sturm_equation (g := deriv W)
    (φ₂ := deriv (deriv φ)) (hVd x hx) hφ.differentiableAt.hasDerivAt
    (hRa x hx).differentiableAt.hasDerivAt (hRa x hx).deriv.differentiableAt.hasDerivAt
    (hHa x hx).differentiableAt.hasDerivAt (hHa x hx).deriv.differentiableAt.hasDerivAt
    hVpos hHpos hφ0 hel
  have he : (fun z => CriticalMode.weight V φ H z * deriv U z) =ᶠ[𝓝 x]
      fun z => CriticalMode.weight V φ H z * CriticalMode.modePrime R (deriv R) H (deriv H) z := by
    have hHp : ∀ᶠ z in 𝓝 x, 0 < H z := (hHa x hx).continuousAt.eventually (Ioi_mem_nhds hHpos)
    filter_upwards [hs.mem_nhds hx, hHp] with z hz hzp
    rw [(CriticalMode.hasDerivAt_mode (hRa z hz).differentiableAt.hasDerivAt
      (hHa z hz).differentiableAt.hasDerivAt hzp).deriv]
    rfl
  dsimp only
  rw [CriticalEnergy.coefficientQ_eq_spatial_derivatives hW hφ]
  exact hd.congr_of_eventuallyEq he

end LeanVerification.AnalyticVariationMode
