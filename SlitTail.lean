import LeanVerification.SlitGrowth
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.SlitContour

theorem continuous_horizontal {f : ℂ → ℂ} {H y : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) (hy : y ≠ 0) :
    Continuous (fun x : ℝ => f ((x : ℂ) + y * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hw : (x : ℂ) + y * Complex.I ∈ domain H := Or.inr (by simpa using hy)
  exact ContinuousAt.comp (f := fun u : ℝ => (u : ℂ) + y * Complex.I)
    (hf.differentiableAt ((isOpen_domain H).mem_nhds hw)).continuousAt (by fun_prop)

theorem aestronglyMeasurable_bank {f : ℂ → ℂ} {u : ℝ → ℂ} {H σ : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) (hσ : σ ≠ 0)
    (hlim : ∀ᵐ t : ℝ, Tendsto
      (fun ε : ℝ => f ((t : ℂ) + (σ * ε : ℝ) * Complex.I)) (𝓝[>] 0) (𝓝 (u t))) :
    AEStronglyMeasurable u volume := by
  let F (ε t : ℝ) := if ε = 0 then (0 : ℂ) else f ((t : ℂ) + (σ * ε : ℝ) * Complex.I)
  have hm (ε : ℝ) : AEStronglyMeasurable (F ε) volume := by
    by_cases he : ε = 0
    · simp only [F, he, if_true]
      exact aestronglyMeasurable_const
    · simp only [F, he, if_false]
      exact (continuous_horizontal hf (mul_ne_zero hσ he)).aestronglyMeasurable
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ)) hm
  filter_upwards [hlim] with t ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε he
  change 0 < ε at he
  simp only [F, ne_of_gt he, if_false]

/-- The bank values inherit the same power decay as the holomorphic
function. No independent bound on the boundary density is assumed. -/
theorem norm_bank_le_of_decay {f : ℂ → ℂ} {u : ℂ} {H σ C α R₀ t : ℝ}
    (hσ : σ ≠ 0) (hC : 0 ≤ C) (hα : 0 < α) (ht : 0 < t) (hR₀ : R₀ ≤ t)
    (hdecay : ∀ w ∈ domain H, R₀ ≤ ‖w‖ → ‖f w‖ ≤ C * ‖w‖ ^ (-α))
    (hlim : Tendsto (fun ε : ℝ => f ((t : ℂ) + (σ * ε : ℝ) * Complex.I))
      (𝓝[>] 0) (𝓝 u)) : ‖u‖ ≤ C * t ^ (-α) := by
  apply le_of_tendsto hlim.norm
  filter_upwards [self_mem_nhdsWithin] with ε he
  change 0 < ε at he
  have hw : (t : ℂ) + (σ * ε : ℝ) * Complex.I ∈ domain H :=
    Or.inr (by simpa using mul_ne_zero hσ he.ne')
  have hnorm : t ≤ ‖(t : ℂ) + (σ * ε : ℝ) * Complex.I‖ := by
    simpa [abs_of_pos ht] using Complex.abs_re_le_norm
      ((t : ℂ) + (σ * ε : ℝ) * Complex.I)
  exact (hdecay _ hw (hR₀.trans hnorm)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ht hnorm (neg_nonpos.mpr hα.le)) hC)

theorem norm_bank_quotient_le_of_decay {f : ℂ → ℂ} {u : ℂ}
    {H σ C α R₀ t z : ℝ}
    (hσ : σ ≠ 0) (hC : 0 ≤ C) (hα : 0 < α) (ht : 0 < t) (hR₀ : R₀ ≤ t)
    (hz : 2 * |z| ≤ t)
    (hdecay : ∀ w ∈ domain H, R₀ ≤ ‖w‖ → ‖f w‖ ≤ C * ‖w‖ ^ (-α))
    (hlim : Tendsto (fun ε : ℝ => f ((t : ℂ) + (σ * ε : ℝ) * Complex.I))
      (𝓝[>] 0) (𝓝 u)) :
    ‖u / ((t : ℂ) - z)‖ ≤ 2 * C * t ^ (-α - 1) := by
  have hden : t / 2 ≤ ‖(t : ℂ) - z‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hz' := le_abs_self z
    exact (by linarith : t / 2 ≤ t - z).trans (le_abs_self _)
  rw [norm_div]
  calc
    _ ≤ (C * t ^ (-α)) / (t / 2) :=
      div_le_div₀ (mul_nonneg hC (Real.rpow_nonneg ht.le _))
        (norm_bank_le_of_decay hσ hC hα ht hR₀ hdecay hlim) (half_pos ht) hden
    _ = _ := by rw [Real.rpow_sub ht, Real.rpow_one]; ring

theorem integrableOn_bank_quotient_tail {f : ℂ → ℂ} {u : ℝ → ℂ}
    {H σ C α R₀ T z : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) (hσ : σ ≠ 0)
    (hC : 0 ≤ C) (hα : 0 < α) (hT : 0 < T) (hR₀ : R₀ ≤ T) (hz : 2 * |z| ≤ T)
    (hdecay : ∀ w ∈ domain H, R₀ ≤ ‖w‖ → ‖f w‖ ≤ C * ‖w‖ ^ (-α))
    (hlim : ∀ᵐ t : ℝ, Tendsto
      (fun ε : ℝ => f ((t : ℂ) + (σ * ε : ℝ) * Complex.I)) (𝓝[>] 0) (𝓝 (u t))) :
    IntegrableOn (fun t => u t / ((t : ℂ) - z)) (Ioi T) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) hT).const_mul (2 * C)
  have hm : AEStronglyMeasurable (fun t => u t / ((t : ℂ) - z)) volume :=
    ((aestronglyMeasurable_bank hf hσ hlim).aemeasurable.div
      ((Complex.continuous_ofReal.sub continuous_const).measurable.aemeasurable)).aestronglyMeasurable
  apply hi.mono' hm.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae hlim] with t ht htl
  exact norm_bank_quotient_le_of_decay hσ hC hα (hT.trans ht) (hR₀.trans ht.le)
    (hz.trans ht.le) hdecay htl

/-- Local bank control and the proved tail estimate discharge the full
improper-integrability condition of the Cauchy representation. -/
theorem integrableOn_bank_quotient {f : ℂ → ℂ} {u : ℝ → ℂ}
    {H σ C α R₀ a z : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) (hσ : σ ≠ 0)
    (hC : 0 ≤ C) (hα : 0 < α) (hza : z < a)
    (hdecay : ∀ w ∈ domain H, R₀ ≤ ‖w‖ → ‖f w‖ ≤ C * ‖w‖ ^ (-α))
    (hlim : ∀ᵐ t : ℝ, Tendsto
      (fun ε : ℝ => f ((t : ℂ) + (σ * ε : ℝ) * Complex.I)) (𝓝[>] 0) (𝓝 (u t)))
    (hloc : ∀ R > a, ∃ η > 0, ∃ b : ℝ → ℝ, IntervalIntegrable b volume a R ∧
      ∀ᵐ t, t ∈ Ioc a R → ∀ ε ∈ Ioo (0 : ℝ) η,
        ‖f ((t : ℂ) + (σ * ε : ℝ) * Complex.I)‖ ≤ b t) :
    IntegrableOn (fun t => u t / ((t : ℂ) - z)) (Ioi a) := by
  let T := max (a + 1) (max 1 (max R₀ (2 * |z|)))
  have haT : a < T := lt_of_lt_of_le (by linarith : a < a + 1) (le_max_left _ _)
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one
    ((le_max_left 1 _).trans (le_max_right _ _))
  have hR₀ : R₀ ≤ T := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hz : 2 * |z| ≤ T := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨η, hη, b, hb, hbound⟩ := hloc T haT
  have hi₁ := integrable_bank_quotient hf hσ hza haT.le hη hb hbound
    (hlim.mono fun t ht _ => ht)
  have hi₂ := integrableOn_bank_quotient_tail hf hσ hC hα hT hR₀ hz hdecay hlim
  have hi := hi₁.1.union hi₂
  simpa only [Ioc_union_Ioi_eq_Ioi haT.le] using hi

end LeanVerification.SlitContour
