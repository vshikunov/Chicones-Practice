import LeanVerification.SlitGrowth
import LeanVerification.SlitLocalBounds

/-! Physical one-sided bank extensions and finite subintegrable singularities
discharge the slit contour's local domination and horizontal-limit premises. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace LeanVerification.SlitContour

set_option maxHeartbeats 800000

def physicalBank (f : ℂ → ℂ) (H : ℝ) (u : ℝ → ℂ) (t : ℝ) : ℂ :=
  if t < H then f (t : ℂ) else u t

theorem localBankControl_of_physical {N : ℕ} {f : ℂ → ℂ} {H a : ℝ}
    (c β : Fin N → ℝ) (hH : H ∈ range c)
    (hf : DifferentiableOn ℂ f (domain H))
    (hβ₀ : ∀ j, 0 ≤ β j) (hβ₁ : ∀ j, β j < 1)
    (hsing : ∀ j, ∃ r > 0, ∃ M ≥ 0, ∀ w ∈ domain H,
      dist w (c j : ℂ) < r → ‖f w‖ ≤ M * dist w (c j : ℂ) ^ (-β j))
    (u l : ℝ → ℂ)
    (hu : ∀ t, H < t → t ∉ range c →
      Tendsto f (𝓝[{w : ℂ | 0 < w.im}] (t : ℂ)) (𝓝 (u t)))
    (hl : ∀ t, H < t → t ∉ range c →
      Tendsto f (𝓝[{w : ℂ | w.im < 0}] (t : ℂ)) (𝓝 (l t))) :
    LocalBankControl f a := by
  intro R hR
  have hreg : ∀ t ∈ Icc a R, t ∉ range c → ∃ r > 0, ∃ M ≥ 0,
      ∀ w ∈ domain H, dist w (t : ℂ) < r → ‖f w‖ ≤ M := by
    intro t _ htc
    rcases lt_or_gt_of_ne (fun he : t = H => htc (he ▸ hH)) with ht | ht
    · exact local_bound_left_of_cut hf ht
    · exact local_bound_of_bank_limits ht (hu t ht htc) (hl t ht htc)
  obtain ⟨η, hη, b, hb, _, hbound⟩ := exists_power_bank_majorant c β hβ₀ hβ₁ hsing hreg
  refine ⟨η, hη, b, hb, ?_⟩
  filter_upwards [hbound] with t ht htm ε hε
  constructor
  · exact ht (Ioc_subset_Icc_self htm) ε (by simpa [abs_of_pos hε.1] using hε.2) hε.1.ne'
  · have he := ht (Ioc_subset_Icc_self htm) (-ε) (by simpa [abs_of_pos hε.1] using hε.2)
      (neg_ne_zero.mpr hε.1.ne')
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using he

theorem tendsto_horizontal_upper (t : ℝ) :
    Tendsto (fun ε : ℝ => (t : ℂ) + ε * Complex.I) (𝓝[>] (0 : ℝ))
      (𝓝[{w : ℂ | 0 < w.im}] (t : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun ε : ℝ => (t : ℂ) + ε * Complex.I) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa using hε

theorem tendsto_horizontal_lower (t : ℝ) :
    Tendsto (fun ε : ℝ => (t : ℂ) - ε * Complex.I) (𝓝[>] (0 : ℝ))
      (𝓝[{w : ℂ | w.im < 0}] (t : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun ε : ℝ => (t : ℂ) - ε * Complex.I) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa using hε

theorem physical_banks_horizontal_limits {N : ℕ} {f : ℂ → ℂ} {H : ℝ}
    (c : Fin N → ℝ) (hH : H ∈ range c)
    (hf : DifferentiableOn ℂ f (domain H)) (u l : ℝ → ℂ)
    (hu : ∀ t, H < t → t ∉ range c →
      Tendsto f (𝓝[{w : ℂ | 0 < w.im}] (t : ℂ)) (𝓝 (u t)))
    (hl : ∀ t, H < t → t ∉ range c →
      Tendsto f (𝓝[{w : ℂ | w.im < 0}] (t : ℂ)) (𝓝 (l t))) :
    ∀ᵐ t : ℝ, Tendsto (fun ε : ℝ => f ((t : ℂ) + ε * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 (physicalBank f H u t)) ∧
      Tendsto (fun ε : ℝ => f ((t : ℂ) - ε * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 (physicalBank f H l t)) := by
  have hn : ∀ᵐ t : ℝ, t ∉ range c := by
    rw [ae_iff]
    simpa only [not_not] using (Set.finite_range c).measure_zero volume
  filter_upwards [hn] with t htc
  rcases lt_or_gt_of_ne (fun he : t = H => htc (he ▸ hH)) with ht | ht
  · have hc := (hf.differentiableAt ((isOpen_domain H).mem_nhds
      (show (t : ℂ) ∈ domain H from Or.inl ht))).continuousAt.tendsto
    simp only [physicalBank, if_pos ht]
    exact ⟨hc.comp ((tendsto_horizontal_upper t).mono_right nhdsWithin_le_nhds),
      hc.comp ((tendsto_horizontal_lower t).mono_right nhdsWithin_le_nhds)⟩
  · simp only [physicalBank, if_neg (not_lt.mpr ht.le)]
    exact ⟨(hu t ht htc).comp (tendsto_horizontal_upper t),
      (hl t ht htc).comp (tendsto_horizontal_lower t)⟩

end LeanVerification.SlitContour
