import LeanVerification.OneSignChangeConvolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
The affine change between the left-convolution and fixed-lag integrals.
The measure-preserving involution s ↦ x - s gives both the exact integral
identity and the equivalence of absolute-integrability conditions.
-/

noncomputable section

open MeasureTheory Set

namespace LeanVerification.Convolution

theorem sub_left_preimage_Iio (x : ℝ) :
    (fun s : ℝ => x - s) ⁻¹' Iio x = Ioi 0 := by
  ext s
  simp only [mem_preimage, mem_Iio, mem_Ioi]
  constructor <;> intro h <;> linarith

theorem leftConvolution_eq_fixed_lag (f K : ℝ → ℝ) (x : ℝ) :
    leftConvolution f K x = ∫ s in Ioi (0 : ℝ), f (x - s) * K s := by
  have he := (Measure.measurePreserving_sub_left (volume : Measure ℝ) x).setIntegral_preimage_emb
    (Homeomorph.subLeft x).measurableEmbedding (fun y => f y * K (x - y)) (Iio x)
  simpa only [sub_left_preimage_Iio, sub_sub_cancel] using he.symm

theorem leftConvolutionSlope_eq_fixed_lag (f K : ℝ → ℝ) (x : ℝ) :
    leftConvolutionSlope f K x = ∫ s in Ioi (0 : ℝ), f (x - s) * deriv K s :=
  leftConvolution_eq_fixed_lag f (deriv K) x

theorem integrable_leftConvolution_iff_fixed_lag (f K : ℝ → ℝ) (x : ℝ) :
    IntegrableOn (fun y => f y * K (x - y)) (Iio x) ↔
      IntegrableOn (fun s => f (x - s) * K s) (Ioi 0) := by
  have he := (Measure.measurePreserving_sub_left (volume : Measure ℝ) x).integrableOn_comp_preimage
    (Homeomorph.subLeft x).measurableEmbedding
      (f := fun y => f y * K (x - y)) (s := Iio x)
  simpa only [sub_left_preimage_Iio, Function.comp_def, sub_sub_cancel] using he.symm

theorem integrable_leftConvolutionSlope_iff_fixed_lag (f K : ℝ → ℝ) (x : ℝ) :
    IntegrableOn (fun y => f y * deriv K (x - y)) (Iio x) ↔
      IntegrableOn (fun s => f (x - s) * deriv K s) (Ioi 0) :=
  integrable_leftConvolution_iff_fixed_lag f (deriv K) x

theorem hasDerivAt_leftConvolution_of_fixed_lag {f K : ℝ → ℝ} {x : ℝ}
    (hd : HasDerivAt (fun y => ∫ s in Ioi (0 : ℝ), f (y - s) * K s)
      (∫ s in Ioi (0 : ℝ), f (x - s) * deriv K s) x) :
    HasDerivAt (leftConvolution f K) (leftConvolutionSlope f K x) x := by
  have heq : leftConvolution f K = fun y => ∫ s in Ioi (0 : ℝ), f (y - s) * K s := by
    funext y
    exact leftConvolution_eq_fixed_lag f K y
  rwa [heq, leftConvolutionSlope_eq_fixed_lag]

end LeanVerification.Convolution
