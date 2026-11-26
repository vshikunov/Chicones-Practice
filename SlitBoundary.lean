import LeanVerification.SlitContour
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.SlitContour

/-- A common integrable bound for both horizontal banks on every finite
interval. This condition is derived from the finite cutpoint power bounds. -/
def LocalBankControl (f : ℂ → ℂ) (a : ℝ) : Prop :=
  ∀ R > a, ∃ η > 0, ∃ b : ℝ → ℝ, IntervalIntegrable b volume a R ∧
    ∀ᵐ t, t ∈ Ioc a R → ∀ ε ∈ Ioo (0 : ℝ) η,
      ‖f ((t : ℂ) + ε * Complex.I)‖ ≤ b t ∧
      ‖f ((t : ℂ) - ε * Complex.I)‖ ≤ b t

theorem continuous_quotient_horizontal {f : ℂ → ℂ} {H z y : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) (hy : y ≠ 0) :
    Continuous (fun x : ℝ => quotient f z ((x : ℂ) + y * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hw : (x : ℂ) + y * Complex.I ∈ domain H := Or.inr (by simpa using hy)
  have hn : (x : ℂ) + y * Complex.I - z ≠ 0 := by
    intro heq
    have him := congrArg Complex.im heq
    simp at him
    exact hy him
  have hc : ContinuousAt (quotient f z) ((x : ℂ) + y * Complex.I) :=
    (hf.differentiableAt ((isOpen_domain H).mem_nhds hw)).continuousAt.div
      (continuousAt_id.sub_const (z : ℂ)) hn
  exact ContinuousAt.comp (f := fun u : ℝ => (u : ℂ) + y * Complex.I) hc (by fun_prop)

theorem norm_quotient_horizontal_le {f : ℂ → ℂ} {a z t y B : ℝ}
    (hza : z < a) (hat : a ≤ t)
    (hb : ‖f ((t : ℂ) + y * Complex.I)‖ ≤ B) :
    ‖quotient f z ((t : ℂ) + y * Complex.I)‖ ≤ B / (a - z) := by
  have hden : a - z ≤ ‖(t : ℂ) + y * Complex.I - z‖ := by
    have hn := Complex.abs_re_le_norm ((t : ℂ) + y * Complex.I - z)
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_self, add_zero] at hn
    rw [abs_of_pos (by linarith : 0 < t - z)] at hn
    linarith
  unfold quotient
  rw [norm_div]
  exact div_le_div₀ ((norm_nonneg _).trans hb) hb (sub_pos.mpr hza) hden

theorem quotient_bank_tendsto {f : ℂ → ℂ} {u : ℂ} {t z σ : ℝ}
    (htz : z < t)
    (hu : Tendsto (fun ε : ℝ => f ((t : ℂ) + (σ * ε : ℝ) * Complex.I))
      (𝓝[>] 0) (𝓝 u)) :
    Tendsto (fun ε : ℝ => quotient f z ((t : ℂ) + (σ * ε : ℝ) * Complex.I))
      (𝓝[>] 0) (𝓝 (u / ((t : ℂ) - z))) := by
  have he : Tendsto (fun ε : ℝ => ((σ * ε : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => ((σ * ε : ℝ) : ℂ)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun ε : ℝ => (t : ℂ) + (σ * ε : ℝ) * Complex.I - z)
      (𝓝[>] 0) (𝓝 ((t : ℂ) - z)) := by
    simpa using (tendsto_const_nhds.add (he.mul_const Complex.I)).sub_const (z : ℂ)
  have hn : (t : ℂ) - z ≠ 0 := by exact_mod_cast sub_ne_zero.mpr htz.ne'
  exact hu.div hd hn

/-- Bank values inherit measurability and integrability from the actual
holomorphic horizontal slices and a local integrable majorant. -/
theorem integrable_bank_quotient {f : ℂ → ℂ} {u : ℝ → ℂ}
    {b : ℝ → ℝ} {H a R z σ η : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) (hσ : σ ≠ 0)
    (hza : z < a) (haR : a ≤ R) (hη : 0 < η)
    (hb : IntervalIntegrable b volume a R)
    (hbound : ∀ᵐ t, t ∈ Ioc a R → ∀ ε ∈ Ioo (0 : ℝ) η,
      ‖f ((t : ℂ) + (σ * ε : ℝ) * Complex.I)‖ ≤ b t)
    (hlim : ∀ᵐ t, t ∈ Ioc a R → Tendsto
      (fun ε : ℝ => f ((t : ℂ) + (σ * ε : ℝ) * Complex.I)) (𝓝[>] 0) (𝓝 (u t))) :
    IntervalIntegrable (fun t => u t / ((t : ℂ) - z)) volume a R := by
  let F (ε t : ℝ) := if ε = 0 then (0 : ℂ)
    else quotient f z ((t : ℂ) + (σ * ε : ℝ) * Complex.I)
  have hm (ε : ℝ) : AEStronglyMeasurable (F ε) (volume.restrict (Ioc a R)) := by
    by_cases he : ε = 0
    · simp only [F, he, if_true]
      exact aestronglyMeasurable_const
    · simp only [F, he, if_false]
      exact (continuous_quotient_horizontal hf (mul_ne_zero hσ he)).aestronglyMeasurable
  have hq : ∀ᵐ t ∂volume.restrict (Ioc a R), Tendsto (fun ε : ℝ => F ε t)
      (𝓝[>] 0) (𝓝 (u t / ((t : ℂ) - z))) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hlim] with t ht htmem
    apply (quotient_bank_tendsto (hza.trans htmem.1) (ht htmem)).congr'
    filter_upwards [self_mem_nhdsWithin] with ε he
    change 0 < ε at he
    simp only [F, ne_of_gt he, if_false]
  have hmeas := aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ)) hm hq
  have hintb : Integrable (fun t => b t / (a - z)) (volume.restrict (Ioc a R)) := by
    simpa only [uIoc_of_le haR] using (hb.div_const (a - z)).def'
  have hi := hintb.mono' hmeas ?_
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le haR).mpr hi
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hbound, hlim] with t ht hl htmem
  have hqt := quotient_bank_tendsto (hza.trans htmem.1) (hl htmem)
  apply le_of_tendsto hqt.norm
  filter_upwards [Ioo_mem_nhdsGT hη] with ε he
  exact norm_quotient_horizontal_le hza htmem.1.le (ht htmem ε he)

/-- The moving banks converge under their derived physical quotient
majorant. Both bank functions are actual boundary limits of `f`. -/
theorem integral_bank_tendsto {f : ℂ → ℂ} {u : ℝ → ℂ}
    {b : ℝ → ℝ} {H a R z σ η : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) (hσ : σ ≠ 0)
    (hza : z < a) (haR : a ≤ R) (hη : 0 < η)
    (hb : IntervalIntegrable b volume a R)
    (hbound : ∀ᵐ t, t ∈ Ioc a R → ∀ ε ∈ Ioo (0 : ℝ) η,
      ‖f ((t : ℂ) + (σ * ε : ℝ) * Complex.I)‖ ≤ b t)
    (hlim : ∀ᵐ t, t ∈ Ioc a R → Tendsto
      (fun ε : ℝ => f ((t : ℂ) + (σ * ε : ℝ) * Complex.I)) (𝓝[>] 0) (𝓝 (u t))) :
    Tendsto (fun ε : ℝ => ∫ t in a..R,
      quotient f z ((t : ℂ) + (σ * ε : ℝ) * Complex.I))
      (𝓝[>] 0) (𝓝 (∫ t in a..R, u t / ((t : ℂ) - z))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => b t / (a - z)) ?_ ?_ (hb.div_const (a - z)) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε he
    exact (continuous_quotient_horizontal hf (mul_ne_zero hσ he.ne')).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT hη] with ε he
    filter_upwards [hbound] with t ht htmem
    rw [uIoc_of_le haR] at htmem
    exact norm_quotient_horizontal_le hza htmem.1.le (ht htmem ε he)
  · filter_upwards [hlim] with t ht htmem
    rw [uIoc_of_le haR] at htmem
    exact quotient_bank_tendsto (hza.trans htmem.1) (ht htmem)

end LeanVerification.SlitContour
