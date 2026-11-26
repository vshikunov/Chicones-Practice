import LeanVerification.LocalSignedGluing

/-! Absolute density encoding of the constructed locally signed input.
The encoding applies to arbitrary Banach-valued absolutely convergent integrals. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace LeanVerification.LocalSigned

variable {α E : Type*} [MeasurableSpace α]

def jordanSign {μ ν : Measure α} (h : μ ⟂ₘ ν) (x : α) : ℝ := by
  classical
  exact if x ∈ h.nullSet then -1 else 1

theorem measurable_jordanSign {μ ν : Measure α} (h : μ ⟂ₘ ν) :
    Measurable (jordanSign h) := by
  classical
  unfold jordanSign
  exact Measurable.ite h.measurableSet_nullSet measurable_const measurable_const

theorem norm_jordanSign {μ ν : Measure α} (h : μ ⟂ₘ ν) (x : α) :
    ‖jordanSign h x‖ = 1 := by
  by_cases hx : x ∈ h.nullSet <;> simp [jordanSign, hx]

theorem jordanSign_mul_self {μ ν : Measure α} (h : μ ⟂ₘ ν) (x : α) :
    jordanSign h x * jordanSign h x = 1 := by
  by_cases hx : x ∈ h.nullSet <;> simp [jordanSign, hx]

theorem jordanSign_eq_one_ae {μ ν : Measure α} (h : μ ⟂ₘ ν) :
    jordanSign h =ᶠ[ae μ] fun _ => 1 := by
  have hn : ∀ᵐ x ∂μ, x ∉ h.nullSet := by
    rw [ae_iff]
    simpa only [not_not] using h.measure_nullSet
  filter_upwards [hn] with x hx
  simp [jordanSign, hx]

theorem jordanSign_eq_neg_one_ae {μ ν : Measure α} (h : μ ⟂ₘ ν) :
    jordanSign h =ᶠ[ae ν] fun _ => -1 := by
  have hn : ∀ᵐ x ∂ν, x ∈ h.nullSet := by
    rw [ae_iff]
    exact h.measure_compl_nullSet
  filter_upwards [hn] with x hx
  simp [jordanSign, hx]

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_jordanSign_smul {μ ν : Measure α} (h : μ ⟂ₘ ν)
    (g : α → E) (x : α) : ‖jordanSign h x • g x‖ = ‖g x‖ := by
  rw [norm_smul, norm_jordanSign, one_mul]

theorem integrable_jordanSign_smul_iff {μ ν ρ : Measure α} (h : μ ⟂ₘ ν)
    (g : α → E) : Integrable (fun x => jordanSign h x • g x) ρ ↔ Integrable g ρ := by
  have forward (f : α → E) (hf : Integrable f ρ) :
      Integrable (fun x => jordanSign h x • f x) ρ := by
    apply hf.mono ((measurable_jordanSign h).aestronglyMeasurable.smul hf.aestronglyMeasurable)
    exact ae_of_all _ fun x => (norm_jordanSign_smul h f x).le
  refine ⟨fun hg => ?_, forward g⟩
  have hgg := forward _ hg
  simpa only [smul_smul, jordanSign_mul_self, one_smul] using hgg

theorem integral_jordanSign_encoding {μ ν : Measure α} (h : μ ⟂ₘ ν)
    {g : α → E} (hg : Integrable g (μ + ν)) :
    (∫ x, jordanSign h x • g x ∂(μ + ν)) = (∫ x, g x ∂μ) - ∫ x, g x ∂ν := by
  have hp := (integrable_add_measure.mp hg).1
  have hn := (integrable_add_measure.mp hg).2
  rw [integral_add_measure ((integrable_jordanSign_smul_iff h g).mpr hp)
    ((integrable_jordanSign_smul_iff h g).mpr hn)]
  have heqp : (∫ x, jordanSign h x • g x ∂μ) = ∫ x, g x ∂μ := by
    apply integral_congr_ae
    filter_upwards [jordanSign_eq_one_ae h] with x hx
    simp [hx]
  have heqn : (∫ x, jordanSign h x • g x ∂ν) = -∫ x, g x ∂ν := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [jordanSign_eq_neg_one_ae h] with x hx
    simp [hx]
  rw [heqp, heqn, sub_eq_add_neg]

theorem glued_density_integral (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) {g : α → E} (hg : Integrable g (variationGlue s ν)) :
    (∫ x, jordanSign (glued_mutuallySingular s ν hs) x • g x ∂variationGlue s ν) =
      (∫ x, g x ∂positiveGlue s ν) - ∫ x, g x ∂negativeGlue s ν :=
  integral_jordanSign_encoding (glued_mutuallySingular s ν hs) hg

theorem glued_reference_encoding (s : ℕ → Set α) (ν : ℕ → SignedMeasure α)
    (hs : ∀ n, MeasurableSet (s n)) (hc : Compatible s ν) :
    SigmaFinite (variationGlue s ν) ∧
    ∃ ε : α → ℝ, Measurable ε ∧ (∀ x, ‖ε x‖ = 1) ∧
      (∀ g : α → E, Integrable (fun x => ε x • g x) (variationGlue s ν) ↔
        Integrable g (variationGlue s ν)) ∧
      (∀ g : α → E, Integrable g (variationGlue s ν) →
        (∫ x, ε x • g x ∂variationGlue s ν) =
          (∫ x, g x ∂positiveGlue s ν) - ∫ x, g x ∂negativeGlue s ν) := by
  refine ⟨variationGlue_sigmaFinite s ν hs hc,
    jordanSign (glued_mutuallySingular s ν hs),
    measurable_jordanSign _, norm_jordanSign _, ?_, ?_⟩
  · intro g
    exact integrable_jordanSign_smul_iff _ g
  · intro g hg
    exact glued_density_integral s ν hs hg

end LeanVerification.LocalSigned
