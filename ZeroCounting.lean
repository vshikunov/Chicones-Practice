import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# A Rolle-theorem consequence used by the natural-gauge argument

This file formalizes a general calculus implication used in Sections 32--33
of the manuscript. It does not formalize the Loud system or establish the
paper's hypothesis about stationary points of its particular gauge.

The main assumption is stated explicitly: the derivative has at most one
zero on the real open interval. Rolle's theorem then excludes three distinct
zeros of the function. A positive multiplier preserves the zero set, giving
the corresponding conclusion for a function represented by a positive gauge.

The zero-count predicates count distinct points and impose no simplicity
or multiplicity condition on the zeros.
-/

namespace LeanVerification.ZeroCounting

open Set

/-- Any two zeros in `s` coincide. -/
def AtMostOneZeroOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ⦃x y : ℝ⦄, x ∈ s → y ∈ s → f x = 0 → f y = 0 → x = y

/-- Among any three zeros in `s`, two coincide. -/
def AtMostTwoZerosOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ⦃x y z : ℝ⦄, x ∈ s → y ∈ s → z ∈ s →
    f x = 0 → f y = 0 → f z = 0 → x = y ∨ x = z ∨ y = z

/-- Three ordered zeros would produce two different derivative zeros. -/
theorem not_three_ordered_zeros_of_deriv_atMostOne
    {f : ℝ → ℝ} {a b x y z : ℝ}
    (hf : DifferentiableOn ℝ f (Ioo a b))
    (hcrit : AtMostOneZeroOn (deriv f) (Ioo a b))
    (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) (hz : z ∈ Ioo a b)
    (hxy : x < y) (hyz : y < z)
    (hfx : f x = 0) (hfy : f y = 0) (hfz : f z = 0) : False := by
  have hxy_sub : Icc x y ⊆ Ioo a b := by
    intro t ht
    exact ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  have hyz_sub : Icc y z ⊆ Ioo a b := by
    intro t ht
    exact ⟨lt_of_lt_of_le hy.1 ht.1, lt_of_le_of_lt ht.2 hz.2⟩
  obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_zero hxy
    (hf.continuousOn.mono hxy_sub) (hfx.trans hfy.symm)
  obtain ⟨d, hd, hdd⟩ := exists_deriv_eq_zero hyz
    (hf.continuousOn.mono hyz_sub) (hfy.trans hfz.symm)
  have hcI : c ∈ Ioo a b := ⟨hx.1.trans hc.1, hc.2.trans hy.2⟩
  have hdI : d ∈ Ioo a b := ⟨hy.1.trans hd.1, hd.2.trans hz.2⟩
  have hcd : c = d := hcrit hcI hdI hdc hdd
  exact (ne_of_lt (hc.2.trans hd.1)) hcd

/-- If the derivative has at most one zero, the function has at most two
distinct zeros on the interval. No closed-interval endpoint assumptions
are needed: Rolle is applied only between proposed interior zeros. -/
theorem atMostTwoZerosOn_of_deriv_atMostOne
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Ioo a b))
    (hcrit : AtMostOneZeroOn (deriv f) (Ioo a b)) :
    AtMostTwoZerosOn f (Ioo a b) := by
  intro x y z hx hy hz hfx hfy hfz
  by_cases hxy : x = y
  · exact Or.inl hxy
  by_cases hxz : x = z
  · exact Or.inr (Or.inl hxz)
  by_cases hyz : y = z
  · exact Or.inr (Or.inr hyz)
  exfalso
  rcases lt_or_gt_of_ne hxy with hxy' | hyx'
  · rcases lt_or_gt_of_ne hyz with hyz' | hzy'
    · exact not_three_ordered_zeros_of_deriv_atMostOne
        hf hcrit hx hy hz hxy' hyz' hfx hfy hfz
    · rcases lt_or_gt_of_ne hxz with hxz' | hzx'
      · exact not_three_ordered_zeros_of_deriv_atMostOne
          hf hcrit hx hz hy hxz' hzy' hfx hfz hfy
      · exact not_three_ordered_zeros_of_deriv_atMostOne
          hf hcrit hz hx hy hzx' hxy' hfz hfx hfy
  · rcases lt_or_gt_of_ne hxz with hxz' | hzx'
    · exact not_three_ordered_zeros_of_deriv_atMostOne
        hf hcrit hy hx hz hyx' hxz' hfy hfx hfz
    · rcases lt_or_gt_of_ne hyz with hyz' | hzy'
      · exact not_three_ordered_zeros_of_deriv_atMostOne
          hf hcrit hy hz hx hyz' hzx' hfy hfz hfx
      · exact not_three_ordered_zeros_of_deriv_atMostOne
          hf hcrit hz hy hx hzy' hyx' hfz hfy hfx

/-- The same result on an unbounded open half-line, as needed for the
canonical physical energy interval `L > M`. -/
theorem atMostTwoZerosOn_Ioi_of_deriv_atMostOne
    {f : ℝ → ℝ} {a : ℝ}
    (hf : DifferentiableOn ℝ f (Ioi a))
    (hcrit : AtMostOneZeroOn (deriv f) (Ioi a)) :
    AtMostTwoZerosOn f (Ioi a) := by
  intro x y z hx hy hz hfx hfy hfz
  let b := max x (max y z) + 1
  have hB : max x (max y z) < b := lt_add_of_pos_right _ zero_lt_one
  have hxB : x < b := (le_max_left x (max y z)).trans_lt hB
  have hyB : y < b :=
    ((le_max_left y z).trans (le_max_right x (max y z))).trans_lt hB
  have hzB : z < b :=
    ((le_max_right y z).trans (le_max_right x (max y z))).trans_lt hB
  have hfB : DifferentiableOn ℝ f (Ioo a b) :=
    hf.mono (fun _ ht => ht.1)
  have hcritB : AtMostOneZeroOn (deriv f) (Ioo a b) := by
    intro u v hu hv hdu hdv
    exact hcrit hu.1 hv.1 hdu hdv
  exact atMostTwoZerosOn_of_deriv_atMostOne hfB hcritB
    ⟨hx, hxB⟩ ⟨hy, hyB⟩ ⟨hz, hzB⟩ hfx hfy hfz

/-- An explicit two-point covering of the zero set, including the cases
with no zeros or only one zero. The two covering points need not differ. -/
theorem exists_pair_covers_zeros
    {f : ℝ → ℝ} {s : Set ℝ} (h : AtMostTwoZerosOn f s) :
    ∃ u v : ℝ, ∀ x ∈ s, f x = 0 → x = u ∨ x = v := by
  classical
  by_cases hex : ∃ u ∈ s, f u = 0
  · obtain ⟨u, hu, hfu⟩ := hex
    by_cases hey : ∃ v ∈ s, f v = 0 ∧ u ≠ v
    · obtain ⟨v, hv, hfv, huv⟩ := hey
      refine ⟨u, v, ?_⟩
      intro x hx hfx
      rcases h hx hu hv hfx hfu hfv with hxu | hxv | huv'
      · exact Or.inl hxu
      · exact Or.inr hxv
      · exact (huv huv').elim
    · refine ⟨u, u, ?_⟩
      intro x hx hfx
      by_cases hxu : x = u
      · exact Or.inl hxu
      · exact (hey ⟨x, hx, hfx, Ne.symm hxu⟩).elim
  · refine ⟨0, 0, ?_⟩
    intro x hx hfx
    exact (hex ⟨x, hx, hfx⟩).elim

/-- A strictly positive multiplier does not add or remove zeros in `s`. -/
theorem positive_multiplier_zero_set
    {f weight : ℝ → ℝ} {s : Set ℝ}
    (hweight : ∀ x ∈ s, 0 < weight x) :
    {x | x ∈ s ∧ weight x * f x = 0} = {x | x ∈ s ∧ f x = 0} := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨hx, hprod⟩
    exact ⟨hx, (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (hweight x hx))⟩
  · rintro ⟨hx, hfx⟩
    exact ⟨hx, by rw [hfx, mul_zero]⟩

/-- The distinct-zero bound is equivalent for a function and any strictly
positive multiple of it. -/
theorem positive_multiplier_atMostTwoZerosOn_iff
    {f weight : ℝ → ℝ} {s : Set ℝ}
    (hweight : ∀ x ∈ s, 0 < weight x) :
    AtMostTwoZerosOn (fun x => weight x * f x) s ↔ AtMostTwoZerosOn f s := by
  constructor
  · intro hgauge x y z hx hy hz hfx hfy hfz
    exact hgauge hx hy hz
      (by simp only [hfx, mul_zero])
      (by simp only [hfy, mul_zero])
      (by simp only [hfz, mul_zero])
  · intro hf x y z hx hy hz hfx hfy hfz
    exact hf hx hy hz
      ((mul_eq_zero.mp hfx).resolve_left (ne_of_gt (hweight x hx)))
      ((mul_eq_zero.mp hfy).resolve_left (ne_of_gt (hweight y hy)))
      ((mul_eq_zero.mp hfz).resolve_left (ne_of_gt (hweight z hz)))

/-- The distinct-zero bound passes from a positive gauge to the original
function. No differentiability assumption on the multiplier is required
for this zero-set statement. -/
theorem atMostTwoZerosOn_of_positive_multiplier
    {f weight : ℝ → ℝ} {s : Set ℝ}
    (hweight : ∀ x ∈ s, 0 < weight x)
    (hgauge : AtMostTwoZerosOn (fun x => weight x * f x) s) :
    AtMostTwoZerosOn f s := by
  exact (positive_multiplier_atMostTwoZerosOn_iff hweight).mp hgauge

/-- The abstract final Rolle step in the manuscript's natural-gauge
argument: a differentiable positive gauge with at most one stationary
point yields at most two distinct zeros of the original function. -/
theorem atMostTwoZerosOn_of_positive_gauge
    {f weight : ℝ → ℝ} {a b : ℝ}
    (hweight : ∀ x ∈ Ioo a b, 0 < weight x)
    (hgauge : DifferentiableOn ℝ (fun x => weight x * f x) (Ioo a b))
    (hcrit : AtMostOneZeroOn (deriv (fun x => weight x * f x)) (Ioo a b)) :
    AtMostTwoZerosOn f (Ioo a b) := by
  exact atMostTwoZerosOn_of_positive_multiplier hweight
    (atMostTwoZerosOn_of_deriv_atMostOne hgauge hcrit)

/-- The positive-gauge conclusion on the full half-line of physical
canonical energies, with uniqueness of the gauge's stationary point
still an explicit assumption. -/
theorem atMostTwoZerosOn_Ioi_of_positive_gauge
    {f weight : ℝ → ℝ} {a : ℝ}
    (hweight : ∀ x ∈ Ioi a, 0 < weight x)
    (hgauge : DifferentiableOn ℝ (fun x => weight x * f x) (Ioi a))
    (hcrit : AtMostOneZeroOn (deriv (fun x => weight x * f x)) (Ioi a)) :
    AtMostTwoZerosOn f (Ioi a) := by
  exact atMostTwoZerosOn_of_positive_multiplier hweight
    (atMostTwoZerosOn_Ioi_of_deriv_atMostOne hgauge hcrit)

end LeanVerification.ZeroCounting
