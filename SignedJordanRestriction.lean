import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-! Restriction of finite signed measures and their canonical Jordan parts. -/

noncomputable section

open MeasureTheory Set

namespace LeanVerification.LocalSigned

variable {α : Type*} [MeasurableSpace α]

def jordanRestrict (j : JordanDecomposition α) (s : Set α) : JordanDecomposition α where
  posPart := j.posPart.restrict s
  negPart := j.negPart.restrict s
  mutuallySingular := ((j.mutuallySingular.restrict s).symm.restrict s).symm

theorem signed_restrict_restrict (ν : SignedMeasure α) {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (ν.restrict s).restrict t = ν.restrict (s ∩ t) := by
  ext u hu
  simp only [VectorMeasure.restrict_apply _ ht hu,
    VectorMeasure.restrict_apply _ hs (hu.inter ht),
    VectorMeasure.restrict_apply _ (hs.inter ht) hu]
  congr 1
  ext x
  simp only [mem_inter_iff]
  tauto

theorem jordanRestrict_toSignedMeasure (j : JordanDecomposition α) {s : Set α}
    (hs : MeasurableSet s) :
    (jordanRestrict j s).toSignedMeasure = j.toSignedMeasure.restrict s := by
  ext u hu
  simp only [JordanDecomposition.toSignedMeasure,
    Measure.toSignedMeasure_sub_apply hu, jordanRestrict,
    VectorMeasure.restrict_apply _ hs hu,
    Measure.toSignedMeasure_sub_apply (hu.inter hs), measureReal_def,
    Measure.restrict_apply hu]

theorem toJordanDecomposition_restrict (ν : SignedMeasure α) {s : Set α}
    (hs : MeasurableSet s) :
    SignedMeasure.toJordanDecomposition (ν.restrict s) = jordanRestrict ν.toJordanDecomposition s := by
  apply JordanDecomposition.toSignedMeasure_injective
  rw [SignedMeasure.toSignedMeasure_toJordanDecomposition,
    jordanRestrict_toSignedMeasure _ hs, SignedMeasure.toSignedMeasure_toJordanDecomposition]

theorem positive_restrict (ν : SignedMeasure α) {s : Set α} (hs : MeasurableSet s) :
    (SignedMeasure.toJordanDecomposition (ν.restrict s)).posPart = ν.toJordanDecomposition.posPart.restrict s := by
  rw [toJordanDecomposition_restrict ν hs]
  rfl

theorem negative_restrict (ν : SignedMeasure α) {s : Set α} (hs : MeasurableSet s) :
    (SignedMeasure.toJordanDecomposition (ν.restrict s)).negPart = ν.toJordanDecomposition.negPart.restrict s := by
  rw [toJordanDecomposition_restrict ν hs]
  rfl

theorem totalVariation_restrict (ν : SignedMeasure α) {s : Set α} (hs : MeasurableSet s) :
    SignedMeasure.totalVariation (ν.restrict s) = ν.totalVariation.restrict s := by
  rw [SignedMeasure.totalVariation, SignedMeasure.totalVariation,
    positive_restrict ν hs, negative_restrict ν hs, Measure.restrict_add]

theorem positive_restrict_eq_of_signed_restrict_eq (ν ξ : SignedMeasure α) {s : Set α}
    (hs : MeasurableSet s) (h : ν.restrict s = ξ.restrict s) :
    ν.toJordanDecomposition.posPart.restrict s = ξ.toJordanDecomposition.posPart.restrict s := by
  rw [← positive_restrict ν hs, h, positive_restrict ξ hs]

theorem negative_restrict_eq_of_signed_restrict_eq (ν ξ : SignedMeasure α) {s : Set α}
    (hs : MeasurableSet s) (h : ν.restrict s = ξ.restrict s) :
    ν.toJordanDecomposition.negPart.restrict s = ξ.toJordanDecomposition.negPart.restrict s := by
  rw [← negative_restrict ν hs, h, negative_restrict ξ hs]

end LeanVerification.LocalSigned
