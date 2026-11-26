import LeanVerification.LocalSignedGluing
import Mathlib.Topology.Compactness.Lindelof

/-! Arbitrary compatible local signed data on an open cover.
Second countability supplies the countable refinement used in the construction. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace LeanVerification.LocalSigned

variable {α ι : Type*} [MeasurableSpace α]

theorem signed_gluing_countable_refinement
    (s : ι → Set α) (ν : ι → SignedMeasure α)
    (hs : ∀ i, MeasurableSet (s i))
    (hc : ∀ i j, (ν i).restrict (s i ∩ s j) = (ν j).restrict (s i ∩ s j))
    (f : ℕ → ι) (hcover : (⋃ n, s (f n)) = univ) :
    ∃! pair : Measure α × Measure α,
      pair.1 ⟂ₘ pair.2 ∧ SigmaFinite (pair.1 + pair.2) ∧
      (∀ i, pair.1.restrict (s i) = (ν i).toJordanDecomposition.posPart.restrict (s i)) ∧
      (∀ i, pair.2.restrict (s i) = (ν i).toJordanDecomposition.negPart.restrict (s i)) := by
  let sf : ℕ → Set α := fun n => s (f n)
  let νf : ℕ → SignedMeasure α := fun n => ν (f n)
  have hsf : ∀ n, MeasurableSet (sf n) := fun n => hs (f n)
  have hcf : Compatible sf νf := fun n m => hc (f n) (f m)
  have hp (i : ι) : (positiveGlue sf νf).restrict (s i) =
      (ν i).toJordanDecomposition.posPart.restrict (s i) := by
    apply measureGlue_restrict_other sf _ hsf (hs i)
      (by simpa only [sf, hcover] using subset_univ (s i))
    intro n
    exact positive_restrict_eq_of_signed_restrict_eq _ _ ((hs (f n)).inter (hs i)) (hc (f n) i)
  have hn (i : ι) : (negativeGlue sf νf).restrict (s i) =
      (ν i).toJordanDecomposition.negPart.restrict (s i) := by
    apply measureGlue_restrict_other sf _ hsf (hs i)
      (by simpa only [sf, hcover] using subset_univ (s i))
    intro n
    exact negative_restrict_eq_of_signed_restrict_eq _ _ ((hs (f n)).inter (hs i)) (hc (f n) i)
  refine ⟨(positiveGlue sf νf, negativeGlue sf νf), ?_, ?_⟩
  · exact ⟨glued_mutuallySingular sf νf hsf, variationGlue_sigmaFinite sf νf hsf hcf, hp, hn⟩
  · intro pair hpair
    apply Prod.ext
    · apply Measure.ext_of_iUnion_eq_univ hcover
      intro n
      rw [hpair.2.2.1 (f n), hp (f n)]
    · apply Measure.ext_of_iUnion_eq_univ hcover
      intro n
      rw [hpair.2.2.2 (f n), hn (f n)]

theorem local_pair_finite_on_chart (s : ι → Set α) (ν : ι → SignedMeasure α)
    {pair : Measure α × Measure α}
    (hp : ∀ i, pair.1.restrict (s i) = (ν i).toJordanDecomposition.posPart.restrict (s i))
    (hn : ∀ i, pair.2.restrict (s i) = (ν i).toJordanDecomposition.negPart.restrict (s i))
    (i : ι) : (pair.1 + pair.2) (s i) < ∞ := by
  have hep := congrArg (fun μ : Measure α => μ univ) (hp i)
  have hen := congrArg (fun μ : Measure α => μ univ) (hn i)
  simp only [Measure.restrict_apply_univ] at hep hen
  rw [Measure.add_apply, hep, hen]
  exact ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, measure_lt_top _ _⟩

theorem signed_gluing_open_cover [TopologicalSpace α] [SecondCountableTopology α]
    [OpensMeasurableSpace α] [Nonempty ι]
    (s : ι → Set α) (ν : ι → SignedMeasure α)
    (hs : ∀ i, IsOpen (s i)) (hcover : (⋃ i, s i) = univ)
    (hc : ∀ i j, (ν i).restrict (s i ∩ s j) = (ν j).restrict (s i ∩ s j)) :
    ∃! pair : Measure α × Measure α,
      pair.1 ⟂ₘ pair.2 ∧ SigmaFinite (pair.1 + pair.2) ∧
      IsLocallyFiniteMeasure (pair.1 + pair.2) ∧
      (∀ i, pair.1.restrict (s i) = (ν i).toJordanDecomposition.posPart.restrict (s i)) ∧
      (∀ i, pair.2.restrict (s i) = (ν i).toJordanDecomposition.negPart.restrict (s i)) := by
  obtain ⟨f, hf⟩ := isLindelof_univ.indexed_countable_subcover s hs (by rw [hcover])
  have hf' : (⋃ n, s (f n)) = univ := top_unique hf
  obtain ⟨pair, hp, huniq⟩ := signed_gluing_countable_refinement s ν
    (fun i => (hs i).measurableSet) hc f hf'
  refine ⟨pair, ⟨hp.1, hp.2.1, ?_, hp.2.2⟩, ?_⟩
  · refine ⟨fun x => ?_⟩
    have hx : x ∈ ⋃ i, s i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨s i, (hs i).mem_nhds hi, local_pair_finite_on_chart s ν hp.2.2.1 hp.2.2.2 i⟩
  · intro other ho
    exact huniq other ⟨ho.1, ho.2.1, ho.2.2.2⟩

end LeanVerification.LocalSigned
