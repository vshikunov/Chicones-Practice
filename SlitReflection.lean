import LeanVerification.SlitContour
import LeanVerification.RealSliceUniqueness
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! Connectedness, Schwarz symmetry, and conjugate bank limits on the physical slit plane. -/

noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.SlitContour

set_option maxHeartbeats 1000000

theorem starConvex_domain (H : ℝ) : StarConvex ℝ ((H - 1 : ℝ) : ℂ) (domain H) := by
  intro z hz a b ha hb hab
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp only [hb0, ha1, one_smul, zero_smul, add_zero]
    exact Or.inl (by simp)
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    rcases hz with hre | him
    · apply Or.inl
      simp only [Complex.add_re, Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
      nlinarith [mul_pos hbpos (sub_pos.mpr hre), congrArg (fun t : ℝ => t * H) hab]
    · apply Or.inr
      simpa only [Complex.add_im, Complex.smul_im, Complex.ofReal_im, smul_eq_mul,
        mul_zero, zero_add] using mul_ne_zero hb0 him

theorem isPathConnected_domain (H : ℝ) : IsPathConnected (domain H) := by
  have hc : ((H - 1 : ℝ) : ℂ) ∈ domain H := Or.inl (by simp)
  apply isPathConnected_iff.mpr
  refine ⟨⟨_, hc⟩, ?_⟩
  intro x hx y hy
  exact (JoinedIn.of_segment_subset ((starConvex_domain H).segment_subset hx)).symm.trans
    (JoinedIn.of_segment_subset ((starConvex_domain H).segment_subset hy))

theorem isPreconnected_domain (H : ℝ) : IsPreconnected (domain H) :=
  (isPathConnected_domain H).isConnected.isPreconnected

theorem star_mem_domain {H : ℝ} {z : ℂ} (hz : z ∈ domain H) : star z ∈ domain H := by
  simpa [domain] using hz

theorem hasDerivAt_reflection {f : ℂ → ℂ} {z d : ℂ} (hf : HasDerivAt f d (star z)) :
    HasDerivAt (fun w : ℂ => star (f (star w))) (star d) z := by
  let c : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
  have hR := c.hasFDerivAt.comp z ((hf.hasFDerivAt.restrictScalars ℝ).comp z c.hasFDerivAt)
  change HasFDerivAt (fun w : ℂ => star (f (star w)))
    ((1 : ℂ →L[ℂ] ℂ).smulRight (star d)) z
  apply hasFDerivAt_of_restrictScalars (𝕜 := ℝ) hR
  ext w
  simp [c, Complex.star_def, mul_comm]

theorem analyticOnNhd_reflection {f : ℂ → ℂ} {H : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) :
    AnalyticOnNhd ℂ (fun w : ℂ => star (f (star w))) (domain H) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_domain H)
  intro z hz
  have hd := (hf (star z) (star_mem_domain hz)).differentiableAt
    ((isOpen_domain H).mem_nhds (star_mem_domain hz))
  exact (hasDerivAt_reflection hd.hasDerivAt).differentiableAt.differentiableWithinAt

theorem reflection_eqOn {f : ℂ → ℂ} {H : ℝ}
    (hf : DifferentiableOn ℂ f (domain H))
    (hreal : ∀ x : ℝ, x < H → (f (x : ℂ)).im = 0) :
    EqOn (fun w : ℂ => star (f (star w))) f (domain H) := by
  apply RealComplexification.eqOn_of_eqOn_real_slice (analyticOnNhd_reflection hf)
    (hf.analyticOnNhd (isOpen_domain H)) (isOpen_domain H) (isPreconnected_domain H)
    (r := H - 1) (Or.inl (by simp))
  intro x hx
  have hxH : x < H := by simpa [domain] using hx
  simp only [Complex.star_def, Complex.conj_ofReal]
  apply Complex.ext
  · simp
  · simp [hreal x hxH]

theorem reflection {f : ℂ → ℂ} {H : ℝ}
    (hf : DifferentiableOn ℂ f (domain H))
    (hreal : ∀ x : ℝ, x < H → (f (x : ℂ)).im = 0)
    {z : ℂ} (hz : z ∈ domain H) : f (star z) = star (f z) := by
  have he := reflection_eqOn hf hreal hz
  simpa only [star_star] using congrArg star he

theorem lower_bank_eq_star_upper {f : ℂ → ℂ} {H t : ℝ} {u l : ℂ}
    (hf : DifferentiableOn ℂ f (domain H))
    (hreal : ∀ x : ℝ, x < H → (f (x : ℂ)).im = 0)
    (hu : Tendsto (fun ε : ℝ => f ((t : ℂ) + ε * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 u))
    (hl : Tendsto (fun ε : ℝ => f ((t : ℂ) - ε * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 l)) :
    l = star u := by
  have hs := continuous_star.continuousAt.tendsto.comp hu
  have he : (fun ε : ℝ => star (f ((t : ℂ) + ε * Complex.I))) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε : ℝ => f ((t : ℂ) - ε * Complex.I) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hz : (t : ℂ) + ε * Complex.I ∈ domain H := by
      apply Or.inr
      simpa using (ne_of_gt hε)
    have hr := reflection hf hreal hz
    simpa [Complex.star_def] using hr.symm
  exact tendsto_nhds_unique hl (hs.congr' he)

end LeanVerification.SlitContour
