import LeanVerification.SlitRepresentation
import LeanVerification.SlitPhysicalBanks
import LeanVerification.SlitCauchyHolomorphic

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.SlitContour

/-- The explicit hypotheses of the physical width-cut theorem. `F` is the
given normalized width; no spectral representation is a field of this data. -/
structure PhysicalCutData (F : ℂ → ℂ) (H : ℝ) where
  height_pos : 0 < H
  count : ℕ
  cutpoint : Fin count → ℝ
  exponent : Fin count → ℝ
  endpoint : H ∈ range cutpoint
  cutpoint_ge : ∀ j, H ≤ cutpoint j
  exponent_nonneg : ∀ j, 0 ≤ exponent j
  exponent_lt_one : ∀ j, exponent j < 1
  holomorphic : DifferentiableOn ℂ F (domain H)
  real_below : ∀ x : ℝ, x < H → (F (x : ℂ)).im = 0
  upper : ℝ → ℂ
  lower : ℝ → ℂ
  upper_limit : ∀ t, H < t → t ∉ range cutpoint →
    Tendsto F (𝓝[{w : ℂ | 0 < w.im}] (t : ℂ)) (𝓝 (upper t))
  lower_limit : ∀ t, H < t → t ∉ range cutpoint →
    Tendsto F (𝓝[{w : ℂ | w.im < 0}] (t : ℂ)) (𝓝 (lower t))
  local_growth : ∀ j, ∃ r > 0, ∃ M ≥ 0, ∀ w ∈ domain H,
    dist w (cutpoint j : ℂ) < r →
      ‖F w‖ ≤ M * dist w (cutpoint j : ℂ) ^ (-exponent j)
  constant : ℝ
  decay_exponent : ℝ
  decay_pos : 0 < decay_exponent
  decay_bound : ℝ
  decay_bound_nonneg : 0 ≤ decay_bound
  decay_start : ℝ
  decay : ∀ w ∈ domain H, decay_start ≤ ‖w‖ →
    ‖F w - (constant : ℂ)‖ ≤ decay_bound * ‖w‖ ^ (-decay_exponent)

namespace PhysicalCutData

def residual {F : ℂ → ℂ} {H : ℝ} (d : PhysicalCutData F H) (w : ℂ) : ℂ :=
  F w - (d.constant : ℂ)

def density {F : ℂ → ℂ} {H : ℝ} (d : PhysicalCutData F H) (t : ℝ) : ℝ :=
  Real.sqrt t * (d.upper t).im

theorem residual_holomorphic {F : ℂ → ℂ} {H : ℝ} (d : PhysicalCutData F H) :
    DifferentiableOn ℂ d.residual (domain H) :=
  d.holomorphic.sub_const (d.constant : ℂ)

theorem residual_local_growth {F : ℂ → ℂ} {H : ℝ} (d : PhysicalCutData F H) :
    ∀ j, ∃ r > 0, ∃ M ≥ 0, ∀ w ∈ domain H,
      dist w (d.cutpoint j : ℂ) < r →
        ‖d.residual w‖ ≤ M * dist w (d.cutpoint j : ℂ) ^ (-d.exponent j) := by
  intro j
  obtain ⟨r, hr, M, hM, hm⟩ := d.local_growth j
  refine ⟨min r 1, lt_min hr zero_lt_one, M + |d.constant|,
    add_nonneg hM (abs_nonneg _), ?_⟩
  intro w hw hd
  have hn : w ≠ (d.cutpoint j : ℂ) := by
    intro he
    rw [he] at hw
    have : d.cutpoint j < H := by simpa [domain] using hw
    exact (not_lt.mpr (d.cutpoint_ge j)) this
  have hp : 1 ≤ dist w (d.cutpoint j : ℂ) ^ (-d.exponent j) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (dist_pos.mpr hn)
      (hd.trans_le (min_le_right _ _)).le (neg_nonpos.mpr (d.exponent_nonneg j))
  have hb := hm w hw (hd.trans_le (min_le_left _ _))
  unfold residual
  calc
    _ ≤ ‖F w‖ + |d.constant| := by simpa using norm_sub_le (F w) (d.constant : ℂ)
    _ ≤ (M + |d.constant|) * dist w (d.cutpoint j : ℂ) ^ (-d.exponent j) := by
      nlinarith [mul_le_mul_of_nonneg_left hp (abs_nonneg d.constant)]

theorem residual_localBankControl {F : ℂ → ℂ} {H : ℝ} (d : PhysicalCutData F H) (a : ℝ) :
    LocalBankControl d.residual a :=
  localBankControl_of_physical d.cutpoint d.exponent d.endpoint d.residual_holomorphic
    d.exponent_nonneg d.exponent_lt_one d.residual_local_growth
    (fun t => d.upper t - (d.constant : ℂ)) (fun t => d.lower t - (d.constant : ℂ))
    (fun t ht htc => (d.upper_limit t ht htc).sub_const (d.constant : ℂ))
    (fun t ht htc => (d.lower_limit t ht htc).sub_const (d.constant : ℂ))

theorem residual_horizontal_limits {F : ℂ → ℂ} {H : ℝ} (d : PhysicalCutData F H) :
    ∀ᵐ t : ℝ,
      Tendsto (fun ε : ℝ => d.residual ((t : ℂ) + ε * Complex.I))
        (𝓝[>] (0 : ℝ))
        (𝓝 (physicalBank d.residual H (fun t => d.upper t - (d.constant : ℂ)) t)) ∧
      Tendsto (fun ε : ℝ => d.residual ((t : ℂ) - ε * Complex.I))
        (𝓝[>] (0 : ℝ))
        (𝓝 (physicalBank d.residual H (fun t => d.lower t - (d.constant : ℂ)) t)) :=
  physical_banks_horizontal_limits d.cutpoint d.endpoint d.residual_holomorphic
    (fun t => d.upper t - (d.constant : ℂ)) (fun t => d.lower t - (d.constant : ℂ))
    (fun t ht htc => (d.upper_limit t ht htc).sub_const (d.constant : ℂ))
    (fun t ht htc => (d.lower_limit t ht htc).sub_const (d.constant : ℂ))

theorem lower_eq_star_upper_ae {F : ℂ → ℂ} {H : ℝ} (d : PhysicalCutData F H) :
    ∀ᵐ t ∂volume.restrict (Ioi H), d.lower t = star (d.upper t) := by
  have hn : ∀ᵐ t : ℝ, t ∉ range d.cutpoint := by
    rw [ae_iff]
    simpa only [not_not] using (Set.finite_range d.cutpoint).measure_zero volume
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hn] with t ht htc
  exact lower_bank_eq_star_upper d.holomorphic d.real_below
    ((d.upper_limit t ht htc).comp (tendsto_horizontal_upper t))
    ((d.lower_limit t ht htc).comp (tendsto_horizontal_lower t))

/-- The contour construction is specialized to the actual supplied banks
and the actual finite cutpoint growth assumptions. -/
theorem real_jump_representation {F : ℂ → ℂ} {H z : ℝ}
    (d : PhysicalCutData F H) (hz : z < H) :
    IntegrableOn (fun t => (d.upper t - d.lower t) / ((t : ℂ) - z)) (Ioi H) ∧
      (∫ t in Ioi H, (d.upper t - d.lower t) / ((t : ℂ) - z)) =
        2 * (Real.pi : ℂ) * Complex.I * (F z - (d.constant : ℂ)) := by
  let a := (z + H) / 2
  have hza : z < a := by dsimp [a]; linarith
  have haH : a < H := by dsimp [a]; linarith
  let U := physicalBank d.residual H (fun t => d.upper t - (d.constant : ℂ))
  let L := physicalBank d.residual H (fun t => d.lower t - (d.constant : ℂ))
  have hr := real_cauchy_representation d.residual_holomorphic hza haH
    d.decay_bound_nonneg d.decay_pos d.decay (d.residual_localBankControl a)
    (d.residual_horizontal_limits.mono (fun t ht => ht.1))
    (d.residual_horizontal_limits.mono (fun t ht => ht.2))
  have hsub : Ioi H ⊆ Ioi a := Ioi_subset_Ioi haH.le
  have he : ∀ t ∈ Ioi H, (U t - L t) / ((t : ℂ) - z) =
      (d.upper t - d.lower t) / ((t : ℂ) - z) := by
    intro t ht
    change H < t at ht
    simp only [U, L, physicalBank, if_neg (not_lt.mpr ht.le)]
    ring
  have hi : IntegrableOn (fun t => (d.upper t - d.lower t) / ((t : ℂ) - z)) (Ioi H) := by
    apply (hr.1.mono_set hsub).congr_fun he measurableSet_Ioi
  refine ⟨hi, ?_⟩
  have hzH : ∀ᵐ t : ℝ, t ≠ H := by
    rw [ae_iff]
    simpa only [not_not] using (measure_singleton H : volume ({H} : Set ℝ) = 0)
  have hzero : ∀ᵐ t : ℝ, t ∈ Ioi a \ Ioi H → (U t - L t) / ((t : ℂ) - z) = 0 := by
    filter_upwards [hzH] with t ht htm
    have htH : t < H := lt_of_le_of_ne (not_lt.mp htm.2) ht
    simp only [U, L, physicalBank, if_pos htH, sub_self, zero_div]
  have hrestrict := setIntegral_eq_of_subset_of_ae_diff_eq_zero
    (μ := volume) measurableSet_Ioi.nullMeasurableSet hsub hzero
  calc
    _ = ∫ t in Ioi H, (U t - L t) / ((t : ℂ) - z) :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => (he t ht).symm)
    _ = ∫ t in Ioi a, (U t - L t) / ((t : ℂ) - z) := hrestrict.symm
    _ = _ := hr.2

theorem integrable_upper_im_quotient {F : ℂ → ℂ} {H z : ℝ}
    (d : PhysicalCutData F H) (hz : z < H) :
    IntegrableOn (fun t => (d.upper t).im / (t - z)) (Ioi H) := by
  let a := (z + H) / 2
  have hza : z < a := by dsimp [a]; linarith
  have haH : a < H := by dsimp [a]; linarith
  have hu : ∀ᵐ t : ℝ, Tendsto
      (fun ε : ℝ => d.residual ((t : ℂ) + ((1 : ℝ) * ε : ℝ) * Complex.I))
      (𝓝[>] 0) (𝓝 (physicalBank d.residual H (fun t => d.upper t - (d.constant : ℂ)) t)) := by
    simpa only [one_mul] using d.residual_horizontal_limits.mono (fun t ht => ht.1)
  have hi := integrableOn_bank_quotient d.residual_holomorphic one_ne_zero
    d.decay_bound_nonneg d.decay_pos hza d.decay hu (d.residual_localBankControl a).upper
  apply ((hi.mono_set (Ioi_subset_Ioi haH.le)).im).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change H < t at ht
  change (physicalBank d.residual H (fun t => d.upper t - (d.constant : ℂ)) t /
      ((t : ℂ) - z)).im = (d.upper t).im / (t - z)
  simp only [physicalBank, if_neg (not_lt.mpr ht.le)]
  rw [← Complex.ofReal_sub, Complex.div_ofReal_im]
  simp

theorem real_width_representation {F : ℂ → ℂ} {H z : ℝ}
    (d : PhysicalCutData F H) (hz : z < H) :
    F z = (d.constant : ℂ) +
      (((1 / Real.pi) * ∫ t in Ioi H, (d.upper t).im / (t - z) : ℝ) : ℂ) := by
  have he := (d.real_jump_representation hz).2
  have hj : (∫ t in Ioi H, (d.upper t - d.lower t) / ((t : ℂ) - z)) =
      (2 * Complex.I) * ((∫ t in Ioi H, (d.upper t).im / (t - z) : ℝ) : ℂ) := by
    have hco : (∫ t in Ioi H, (((d.upper t).im / (t - z) : ℝ) : ℂ)) =
        ((∫ t in Ioi H, (d.upper t).im / (t - z) : ℝ) : ℂ) := integral_complex_ofReal
    rw [← hco, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [d.lower_eq_star_upper_ae] with t ht
    rw [ht]
    have hid : d.upper t - star (d.upper t) = 2 * Complex.I * ((d.upper t).im : ℂ) := by
      apply Complex.ext <;> simp [Complex.star_def]
      <;> ring
    rw [hid, Complex.ofReal_div, Complex.ofReal_sub]
    ring
  rw [hj] at he
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) Complex.I_ne_zero))
  field_simp
  linear_combination -he

theorem density_weight {F : ℂ → ℂ} {H t : ℝ}
    (d : PhysicalCutData F H) (ht : 0 < t) :
    d.density t * t ^ (-(3 : ℝ) / 2) = (d.upper t).im / t := by
  rw [density, Real.sqrt_eq_rpow]
  rw [mul_right_comm, ← Real.rpow_add ht]
  norm_num
  rw [Real.rpow_neg_one]
  ring

/-- The physical signed boundary density has the required weighted mass
as a consequence of the contour hypotheses. -/
theorem integrable_weighted_density {F : ℂ → ℂ} {H : ℝ}
    (d : PhysicalCutData F H) :
    IntegrableOn (fun t => d.density t * t ^ (-(3 : ℝ) / 2)) (Ioi H) := by
  have hi := d.integrable_upper_im_quotient d.height_pos
  apply hi.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simpa only [sub_zero] using (density_weight d (d.height_pos.trans ht)).symm

theorem aestronglyMeasurable_upper_im {F : ℂ → ℂ} {H : ℝ}
    (d : PhysicalCutData F H) :
    AEStronglyMeasurable (fun t => (d.upper t).im) (volume.restrict (Ioi H)) := by
  have hi := d.integrable_upper_im_quotient d.height_pos
  have hm := hi.aestronglyMeasurable.mul measurable_id.aestronglyMeasurable
  apply hm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [sub_zero]
  exact div_mul_cancel₀ _ (d.height_pos.trans ht).ne'

theorem aestronglyMeasurable_density {F : ℂ → ℂ} {H : ℝ}
    (d : PhysicalCutData F H) :
    AEStronglyMeasurable d.density (volume.restrict (Ioi H)) :=
  Real.continuous_sqrt.aestronglyMeasurable.mul d.aestronglyMeasurable_upper_im

theorem integrable_upper_im_absolute_mass {F : ℂ → ℂ} {H : ℝ}
    (d : PhysicalCutData F H) :
    IntegrableOn (fun t => ‖((d.upper t).im : ℂ)‖ / t) (Ioi H) := by
  have hi := (d.integrable_upper_im_quotient d.height_pos).norm
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [sub_zero, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (d.height_pos.trans ht)]

/-- The full holomorphic physical cut representation follows from the
constructed contour formula and analytic continuation on the slit domain. -/
theorem complex_width_representation {F : ℂ → ℂ} {H : ℝ}
    (d : PhysicalCutData F H) {z : ℂ} (hz : z ∈ domain H) :
    F z = (d.constant : ℂ) + (1 / (Real.pi : ℂ)) *
      ∫ t in Ioi H, ((d.upper t).im : ℂ) / ((t : ℂ) - z) := by
  have hΓ : AEStronglyMeasurable (fun t => ((d.upper t).im : ℂ))
      (volume.restrict (Ioi H)) :=
    (Complex.continuous_ofReal.measurable.comp_aemeasurable
      d.aestronglyMeasurable_upper_im.aemeasurable).aestronglyMeasurable
  have hsupp : ∀ᵐ t ∂volume.restrict (Ioi H), H ≤ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ht.le
  have he : ∀ x : ℝ, x < H → d.residual (x : ℂ) =
      (1 / (Real.pi : ℂ)) * cauchyIntegral (volume.restrict (Ioi H))
        (fun t => ((d.upper t).im : ℂ)) (x : ℂ) := by
    intro x hx
    have hc : cauchyIntegral (volume.restrict (Ioi H))
        (fun t => ((d.upper t).im : ℂ)) (x : ℂ) =
        ((∫ t in Ioi H, (d.upper t).im / (t - x) : ℝ) : ℂ) := by
      unfold cauchyIntegral
      simp only [← Complex.ofReal_sub, ← Complex.ofReal_div]
      exact integral_complex_ofReal
    rw [hc]
    have hreal := d.real_width_representation hx
    unfold residual
    push_cast at hreal
    linear_combination hreal
  have h := eqOn_cauchy_of_real_axis (1 / (Real.pi : ℂ)) d.height_pos hΓ hsupp
    d.integrable_upper_im_absolute_mass d.residual_holomorphic he hz
  unfold residual cauchyIntegral at h
  linear_combination h

theorem complex_width_density_representation {F : ℂ → ℂ} {H : ℝ}
    (d : PhysicalCutData F H) {z : ℂ} (hz : z ∈ domain H) :
    F z = (d.constant : ℂ) + (1 / (Real.pi : ℂ)) *
      ∫ t in Ioi H, (d.density t : ℂ) /
        ((Real.sqrt t : ℂ) * ((t : ℂ) - z)) := by
  rw [d.complex_width_representation hz]
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hs : (Real.sqrt t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (d.height_pos.trans ht)).ne'
  rw [div_mul_eq_div_div]
  congr 1
  simp only [density, Complex.ofReal_mul]
  exact (mul_div_cancel_left₀ _ hs).symm

end PhysicalCutData

end LeanVerification.SlitContour
