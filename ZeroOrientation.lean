import LeanVerification.ZeroCounting
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Positive orientation at every zero forces uniqueness

The derivative is assumed positive only at zeros, not throughout the
interval. A boundary comparison prevents a nonnegative function from
crossing down through zero. A later zero would have a nonpositive left
derivative, contradicting its prescribed positive orientation.

The final corollaries combine this result with the existing Rolle argument:
positive curvature at every stationary point implies at most two distinct
zeros, provided the function and its derivative are differentiable on the
stated interval. No regional estimate for a particular Loud integral is
asserted here.
-/

namespace LeanVerification.ZeroOrientation

open Set Filter ZeroCounting
open scoped Topology

/-- A nonnegative initial value remains nonnegative when every zero has
strictly positive derivative. The derivative need not be positive elsewhere. -/
theorem nonneg_on_Icc_of_deriv_pos_at_zeros
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hzero : ∀ t ∈ Icc a b, f t = 0 → 0 < deriv f t)
    (ha : 0 ≤ f a) : ∀ t ∈ Icc a b, 0 ≤ f t := by
  have hc : ContinuousOn (fun t => -f t) (Icc a b) := by
    intro t ht
    exact (hf t ht).continuousAt.neg.continuousWithinAt
  have hbound : ∀ ⦃t⦄, t ∈ Icc a b → -f t ≤ 0 :=
    image_le_of_deriv_right_lt_deriv_boundary
      (f' := fun t => -deriv f t) (B := fun _ => 0) (B' := fun _ => 0)
      hc
      (fun t ht => ((hf t (Ico_subset_Icc_self ht)).hasDerivAt.neg).hasDerivWithinAt)
      (neg_nonpos.mpr ha)
      (fun t => hasDerivAt_const t 0)
      (fun t ht heq => neg_neg_of_pos
        (hzero t (Ico_subset_Icc_self ht) (neg_eq_zero.mp heq)))
  intro t ht
  exact neg_nonpos.mp (hbound ht)

theorem not_two_ordered_zeros_of_deriv_pos_at_zeros
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hzero : ∀ t ∈ Icc a b, f t = 0 → 0 < deriv f t)
    (hfa : f a = 0) (hfb : f b = 0) : False := by
  have hnonneg := nonneg_on_Icc_of_deriv_pos_at_zeros hf hzero (le_of_eq hfa.symm)
  have hd := (hf b ⟨hab.le, le_rfl⟩).hasDerivAt
  have hlim : Tendsto (slope f b) (𝓝[<] b) (𝓝 (deriv f b)) :=
    (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsLT_le_nhdsNE b)
  have hslopes : ∀ᶠ t in 𝓝[<] b, slope f b t ≤ 0 := by
    filter_upwards [Ico_mem_nhdsLT hab] with t ht
    rw [slope_def_field, hfb, sub_zero]
    exact div_nonpos_of_nonneg_of_nonpos (hnonneg t ⟨ht.1, ht.2.le⟩)
      (sub_nonpos.mpr ht.2.le)
  have hle : deriv f b ≤ 0 := le_of_tendsto hlim hslopes
  exact (not_le_of_gt (hzero b ⟨hab.le, le_rfl⟩ hfb)) hle

/-- A real differentiable function has at most one zero on a convex set
if its derivative is strictly positive at every zero in that set. -/
theorem atMostOneZeroOn_of_deriv_pos_at_zeros
    {f : ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ t ∈ s, DifferentiableAt ℝ f t)
    (hzero : ∀ t ∈ s, f t = 0 → 0 < deriv f t) : AtMostOneZeroOn f s := by
  intro x y hx hy hfx hfy
  have hordered : ∀ {u v : ℝ}, u ∈ s → v ∈ s →
      f u = 0 → f v = 0 → u < v → False := by
    intro u v hu hv hfu hfv huv
    have hsub : Icc u v ⊆ s := hs.ordConnected.out hu hv
    exact not_two_ordered_zeros_of_deriv_pos_at_zeros huv
      (fun t ht => hf t (hsub ht))
      (fun t ht => hzero t (hsub ht)) hfu hfv
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact False.elim (hordered hx hy hfx hfy hlt)
  · exact heq
  · exact False.elim (hordered hy hx hfy hfx hgt)

theorem atMostOneZeroOn_Ioo_of_deriv_pos_at_zeros
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Ioo a b))
    (hzero : ∀ t ∈ Ioo a b, f t = 0 → 0 < deriv f t) :
    AtMostOneZeroOn f (Ioo a b) :=
  atMostOneZeroOn_of_deriv_pos_at_zeros (convex_Ioo a b)
    (fun t ht => (hf t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)) hzero

theorem atMostOneZeroOn_Ioi_of_deriv_pos_at_zeros
    {f : ℝ → ℝ} {a : ℝ}
    (hf : DifferentiableOn ℝ f (Ioi a))
    (hzero : ∀ t ∈ Ioi a, f t = 0 → 0 < deriv f t) :
    AtMostOneZeroOn f (Ioi a) :=
  atMostOneZeroOn_of_deriv_pos_at_zeros (convex_Ioi a)
    (fun t ht => (hf t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)) hzero

/-- Positive curvature at every stationary point supplies the stationary
point uniqueness needed by Rolle's theorem. -/
theorem atMostTwoZerosOn_Ioo_of_stationary_positive_curvature
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Ioo a b))
    (hdf : DifferentiableOn ℝ (deriv f) (Ioo a b))
    (hcurv : ∀ t ∈ Ioo a b, deriv f t = 0 → 0 < deriv (deriv f) t) :
    AtMostTwoZerosOn f (Ioo a b) :=
  atMostTwoZerosOn_of_deriv_atMostOne hf
    (atMostOneZeroOn_Ioo_of_deriv_pos_at_zeros hdf hcurv)

theorem atMostTwoZerosOn_Ioi_of_stationary_positive_curvature
    {f : ℝ → ℝ} {a : ℝ}
    (hf : DifferentiableOn ℝ f (Ioi a))
    (hdf : DifferentiableOn ℝ (deriv f) (Ioi a))
    (hcurv : ∀ t ∈ Ioi a, deriv f t = 0 → 0 < deriv (deriv f) t) :
    AtMostTwoZerosOn f (Ioi a) :=
  atMostTwoZerosOn_Ioi_of_deriv_atMostOne hf
    (atMostOneZeroOn_Ioi_of_deriv_pos_at_zeros hdf hcurv)

end LeanVerification.ZeroOrientation
