import LeanVerification.ZeroOrientation
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Critical-mode differential and boundary foundations

This file proves general differential consequences used in revision 10,
Section 4. The input variational equation is explicit. Constructing that
equation from the actual jointly analytic flight clocks is a separate
application, not an assumption hidden in a claimed Loud theorem.
-/

namespace LeanVerification.CriticalMode

open Set Filter Asymptotics
open scoped Topology

/-- At a simple turn the regular energy variation has value `1/g`. -/
theorem variation_value_at_turn {V g Y Y₁ : ℝ}
    (hV : V = 0) (hg : g ≠ 0) (h : 2 * V * Y₁ + g * Y = 1) :
    Y = 1 / g := by
  rw [hV] at h
  apply (eq_div_iff hg).2
  nlinarith [h]

/-- The first variation has positive derivative at every interior zero. -/
theorem variation_derivative_pos_at_zero {V g Y Y₁ : ℝ}
    (hV : 0 < V) (hY : Y = 0) (h : 2 * V * Y₁ + g * Y = 1) :
    0 < Y₁ := by
  rw [hY] at h
  nlinarith

/-- Differentiate the actual first-order variational equation on an open
spatial domain; the second-order equation is a conclusion. -/
theorem variation_second_equation
    {V g g₁ Y Y₁ Y₂ : ℝ → ℝ} {s : Set ℝ} {x : ℝ}
    (hs : IsOpen s) (hx : x ∈ s)
    (hV : HasDerivAt V (-g x) x) (hg : HasDerivAt g (g₁ x) x)
    (hY : HasDerivAt Y (Y₁ x) x) (hY₁ : HasDerivAt Y₁ (Y₂ x) x)
    (heq : ∀ z ∈ s, 2 * V z * Y₁ z + g z * Y z = 1) :
    2 * V x * Y₂ x - g x * Y₁ x + g₁ x * Y x = 0 := by
  have hd := ((hV.const_mul 2).mul hY₁).add (hg.mul hY)
  have he : (fun z => 2 * V z * Y₁ z + g z * Y z) =ᶠ[𝓝 x]
      (fun _ => (1 : ℝ)) := by
    filter_upwards [hs.mem_nhds hx] with z hz
    exact heq z hz
  have hc := hd.congr_of_eventuallyEq he.symm
  have hzero := hc.unique (hasDerivAt_const x (1 : ℝ))
  nlinarith [hzero]

/-- The second variational equation fixes the derivative at a regular turn. -/
theorem variation_derivative_at_turn {V g g₁ Y Y₁ Y₂ : ℝ}
    (hV : V = 0) (hg : g ≠ 0)
    (hfirst : 2 * V * Y₁ + g * Y = 1)
    (hsecond : 2 * V * Y₂ - g * Y₁ + g₁ * Y = 0) :
    Y₁ = g₁ / g ^ 2 := by
  have hY := variation_value_at_turn hV hg hfirst
  rw [hV, hY] at hsecond
  apply (eq_div_iff (pow_ne_zero 2 hg)).2
  field_simp [hg] at hsecond
  nlinarith [hsecond]

noncomputable def auxiliary (V g g₁ φ φ₁ φ₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  φ x * g₁ x - φ₁ x * g x + 2 * V x * φ₂ x

noncomputable def bracket (φ φ₁ Y Y₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  φ x * Y₁ x - φ₁ x * Y x

/-- The derivative of the Wronskian-type bracket is obtained from the
ordinary product rule; the mixed first-derivative terms cancel. -/
theorem hasDerivAt_bracket {φ φ₁ φ₂ Y Y₁ Y₂ : ℝ → ℝ} {x : ℝ}
    (hφ : HasDerivAt φ (φ₁ x) x) (hφ₁ : HasDerivAt φ₁ (φ₂ x) x)
    (hY : HasDerivAt Y (Y₁ x) x) (hY₁ : HasDerivAt Y₁ (Y₂ x) x) :
    HasDerivAt (bracket φ φ₁ Y Y₁) (φ x * Y₂ x - φ₂ x * Y x) x := by
  unfold bracket
  convert (hφ.mul hY₁).sub (hφ₁.mul hY) using 1
  ring

/-- The derivative of the auxiliary coefficient, with `V'=-g`. -/
theorem hasDerivAt_auxiliary
    {V g g₁ g₂ φ φ₁ φ₂ φ₃ : ℝ → ℝ} {x : ℝ}
    (hV : HasDerivAt V (-g x) x)
    (hg : HasDerivAt g (g₁ x) x) (hg₁ : HasDerivAt g₁ (g₂ x) x)
    (hφ : HasDerivAt φ (φ₁ x) x) (hφ₁ : HasDerivAt φ₁ (φ₂ x) x)
    (hφ₂ : HasDerivAt φ₂ (φ₃ x) x) :
    HasDerivAt (auxiliary V g g₁ φ φ₁ φ₂)
      (φ x * g₂ x - 3 * g x * φ₂ x + 2 * V x * φ₃ x) x := by
  unfold auxiliary
  convert ((hφ.mul hg₁).sub (hφ₁.mul hg)).add
    ((hV.const_mul 2).mul hφ₂) using 1
  ring

/-- First critical-mode elimination, without division by the kinetic gap. -/
theorem bracket_first_equation_algebra
    (V g g₁ φ φ₁ φ₂ Y Y₁ Y₂ : ℝ)
    (hsecond : 2 * V * Y₂ - g * Y₁ + g₁ * Y = 0) :
    2 * V * (φ * Y₂ - φ₂ * Y) =
      g * (φ * Y₁ - φ₁ * Y) - (φ * g₁ - φ₁ * g + 2 * V * φ₂) * Y := by
  linear_combination φ * hsecond

/-- The first bracket equation is a genuine derivative identity. -/
theorem bracket_first_equation
    {V g g₁ φ φ₁ φ₂ Y Y₁ Y₂ : ℝ → ℝ} {x : ℝ}
    (hφ : HasDerivAt φ (φ₁ x) x) (hφ₁ : HasDerivAt φ₁ (φ₂ x) x)
    (hY : HasDerivAt Y (Y₁ x) x) (hY₁ : HasDerivAt Y₁ (Y₂ x) x)
    (hsecond : 2 * V x * Y₂ x - g x * Y₁ x + g₁ x * Y x = 0) :
    2 * V x * deriv (bracket φ φ₁ Y Y₁) x =
      g x * bracket φ φ₁ Y Y₁ x - auxiliary V g g₁ φ φ₁ φ₂ x * Y x := by
  rw [(hasDerivAt_bracket hφ hφ₁ hY hY₁).deriv]
  exact bracket_first_equation_algebra _ _ _ _ _ _ _ _ _ hsecond

/-- The regular bracket has a positive endpoint value whenever `H>0`. -/
theorem bracket_value_at_turn {V g g₁ φ φ₁ φ₂ Y Y₁ Y₂ : ℝ}
    (hV : V = 0) (hg : g ≠ 0)
    (hfirst : 2 * V * Y₁ + g * Y = 1)
    (hsecond : 2 * V * Y₂ - g * Y₁ + g₁ * Y = 0) :
    φ * Y₁ - φ₁ * Y = (φ * g₁ - φ₁ * g + 2 * V * φ₂) / g ^ 2 := by
  rw [variation_value_at_turn hV hg hfirst,
    variation_derivative_at_turn hV hg hfirst hsecond, hV]
  field_simp [hg]
  ring

/-- Strict initial positivity and positive derivatives at zeros prevent a
first zero, including the right endpoint. -/
theorem pos_on_Icc_of_deriv_pos_at_zeros
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hzero : ∀ t ∈ Icc a b, f t = 0 → 0 < deriv f t)
    (ha : 0 < f a) : ∀ t ∈ Icc a b, 0 < f t := by
  have hnonneg := ZeroOrientation.nonneg_on_Icc_of_deriv_pos_at_zeros hf hzero ha.le
  intro t ht
  have hge := hnonneg t ht
  by_contra hn
  have hft : f t = 0 := le_antisymm (le_of_not_gt hn) hge
  have hat : a < t := by
    rcases ht.1.eq_or_lt with he | he
    · have : f a = 0 := by simpa [he] using hft
      exact False.elim (ne_of_gt ha this)
    · exact he
  have hlim : Tendsto (slope f t) (𝓝[<] t) (𝓝 (deriv f t)) :=
    (hasDerivAt_iff_tendsto_slope.mp (hf t ht).hasDerivAt).mono_left
      (nhdsLT_le_nhdsNE t)
  have hslopes : ∀ᶠ z in 𝓝[<] t, slope f t z ≤ 0 := by
    filter_upwards [Ico_mem_nhdsLT hat] with z hz
    rw [slope_def_field, hft, sub_zero]
    exact div_nonpos_of_nonneg_of_nonpos
      (hnonneg z ⟨hz.1, hz.2.le.trans ht.2⟩) (sub_nonpos.mpr hz.2.le)
  exact (not_le_of_gt (hzero t ht hft)) (le_of_tendsto hlim hslopes)

/-- The same positivity principle with orientation reversed. -/
theorem pos_on_Icc_of_deriv_neg_at_zeros
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hzero : ∀ t ∈ Icc a b, f t = 0 → deriv f t < 0)
    (hb : 0 < f b) : ∀ t ∈ Icc a b, 0 < f t := by
  have hmem : ∀ t ∈ Icc (-b) (-a), -t ∈ Icc a b := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hd : ∀ t ∈ Icc (-b) (-a),
      HasDerivAt (fun z => f (-z)) (-deriv f (-t)) t := by
    intro t ht
    convert ((hf (-t) (hmem t ht)).hasDerivAt).comp t (hasDerivAt_neg t) using 1
    simp
  have hp := pos_on_Icc_of_deriv_pos_at_zeros
    (fun t ht => (hd t ht).differentiableAt)
    (fun t ht hz => by
      rw [(hd t ht).deriv]
      exact neg_pos.mpr (hzero (-t) (hmem t ht) hz))
    (by simpa using hb)
  intro t ht
  simpa using hp (-t) (show -t ∈ Icc (-b) (-a) by
    constructor <;> linarith [ht.1, ht.2])

/-- Opposite endpoint signs and the variational equation give exactly one
zero; the signs on its two sides are also conclusions. -/
theorem variation_unique_zero_and_signs
    {V g Y Y₁ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hY : ∀ x ∈ Icc a b, HasDerivAt Y (Y₁ x) x)
    (hV : ∀ x ∈ Ioo a b, 0 < V x)
    (heq : ∀ x ∈ Ioo a b, 2 * V x * Y₁ x + g x * Y x = 1)
    (ha : Y a < 0) (hb : 0 < Y b) :
    ∃ c ∈ Ioo a b, Y c = 0 ∧
      (∀ x ∈ Ico a c, Y x < 0) ∧ (∀ x ∈ Ioc c b, 0 < Y x) := by
  have hcont : ContinuousOn Y (Icc a b) := fun x hx =>
    (hY x hx).continuousAt.continuousWithinAt
  have huniq : ZeroCounting.AtMostOneZeroOn Y (Ioo a b) :=
    ZeroOrientation.atMostOneZeroOn_Ioo_of_deriv_pos_at_zeros
      (fun x hx => (hY x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt)
      (fun x hx hz => by
        rw [(hY x (Ioo_subset_Icc_self hx)).deriv]
        exact variation_derivative_pos_at_zero (hV x hx) hz (heq x hx))
  obtain ⟨c, hc, hcz⟩ := intermediate_value_Icc hab.le hcont ⟨ha.le, hb.le⟩
  have hac : a < c := by
    rcases hc.1.eq_or_lt with he | he
    · subst c
      exact False.elim (ne_of_lt ha hcz)
    · exact he
  have hcb : c < b := by
    rcases hc.2.eq_or_lt with he | he
    · subst c
      exact False.elim (ne_of_gt hb hcz)
    · exact he
  refine ⟨c, ⟨hac, hcb⟩, hcz, ?_, ?_⟩
  · intro x hx
    by_contra hn
    have hyx : 0 ≤ Y x := le_of_not_gt hn
    have hsub : Icc a x ⊆ Icc a b := by
      intro z hz
      exact ⟨hz.1, hz.2.trans (hx.2.le.trans hcb.le)⟩
    obtain ⟨z, hz, hzz⟩ := intermediate_value_Icc hx.1 (hcont.mono hsub) ⟨ha.le, hyx⟩
    have haz : a < z := by
      rcases hz.1.eq_or_lt with he | he
      · subst z
        exact False.elim (ne_of_lt ha hzz)
      · exact he
    have hzc : z < c := hz.2.trans_lt hx.2
    have hsame := huniq ⟨haz, hzc.trans hcb⟩ ⟨hac, hcb⟩ hzz hcz
    exact (ne_of_lt hzc) hsame
  · intro x hx
    by_contra hn
    have hyx : Y x ≤ 0 := le_of_not_gt hn
    have hsub : Icc x b ⊆ Icc a b := by
      intro z hz
      exact ⟨(hac.le.trans hx.1.le).trans hz.1, hz.2⟩
    obtain ⟨z, hz, hzz⟩ := intermediate_value_Icc hx.2 (hcont.mono hsub) ⟨hyx, hb.le⟩
    have hzb : z < b := by
      rcases hz.2.eq_or_lt with he | he
      · subst z
        exact False.elim (ne_of_gt hb hzz)
      · exact he
    have hcz' : c < z := hx.1.trans_le hz.1
    have hsame := huniq ⟨hac.trans hcz', hzb⟩ ⟨hac, hcb⟩ hzz hcz
    exact (ne_of_gt hcz') hsame

/-- First-order bracket dynamics prevent a zero on either side of the
single variation zero. Neither the sign of `g` nor that of `R'` away
from zeros is prescribed. -/
theorem bracket_positive_from_first_equation
    {V g H Y R : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b)
    (hR : ∀ x ∈ Icc a b, DifferentiableAt ℝ R x)
    (hV : ∀ x ∈ Ioo a b, 0 < V x)
    (hH : ∀ x ∈ Icc a b, 0 < H x)
    (heq : ∀ x ∈ Ioo a b, 2 * V x * deriv R x = g x * R x - H x * Y x)
    (hneg : ∀ x ∈ Ico a c, Y x < 0)
    (hpos : ∀ x ∈ Ioc c b, 0 < Y x)
    (ha : 0 < R a) (hc : 0 < R c) (hb : 0 < R b) :
    ∀ x ∈ Icc a b, 0 < R x := by
  have hleft : ∀ x ∈ Icc a c, 0 < R x := by
    apply pos_on_Icc_of_deriv_pos_at_zeros
      (fun x hx => hR x ⟨hx.1, hx.2.trans hcb.le⟩) _ ha
    intro x hx hz
    have hax : a < x := by
      rcases hx.1.eq_or_lt with he | he
      · subst x
        exact False.elim (ne_of_gt ha hz)
      · exact he
    have hxc : x < c := by
      rcases hx.2.eq_or_lt with he | he
      · subst x
        exact False.elim (ne_of_gt hc hz)
      · exact he
    have hinside : x ∈ Ioo a b := ⟨hax, hxc.trans hcb⟩
    have hv := hV x hinside
    have hh := hH x (Ioo_subset_Icc_self hinside)
    have hy := hneg x ⟨hx.1, hxc⟩
    have hhY : 0 < H x * (-Y x) := mul_pos hh (neg_pos.mpr hy)
    have he := heq x hinside
    rw [hz] at he
    nlinarith
  have hright : ∀ x ∈ Icc c b, 0 < R x := by
    apply pos_on_Icc_of_deriv_neg_at_zeros
      (fun x hx => hR x ⟨hac.le.trans hx.1, hx.2⟩) _ hb
    intro x hx hz
    have hcx : c < x := by
      rcases hx.1.eq_or_lt with he | he
      · subst x
        exact False.elim (ne_of_gt hc hz)
      · exact he
    have hxb : x < b := by
      rcases hx.2.eq_or_lt with he | he
      · subst x
        exact False.elim (ne_of_gt hb hz)
      · exact he
    have hinside : x ∈ Ioo a b := ⟨hac.trans hcx, hxb⟩
    have hv := hV x hinside
    have hh := hH x (Ioo_subset_Icc_self hinside)
    have hy := hpos x ⟨hcx, hx.2⟩
    have hhY : 0 < H x * Y x := mul_pos hh hy
    have he := heq x hinside
    rw [hz] at he
    nlinarith
  intro x hx
  rcases le_total x c with h | h
  · exact hleft x ⟨hx.1, h⟩
  · exact hright x ⟨h, hx.2⟩

/-- At a variation zero the bracket is positive, using the positive
auxiliary spatial function and the first variational equation. -/
theorem bracket_pos_at_variation_zero {V g φ φ₁ Y Y₁ : ℝ}
    (hV : 0 < V) (hφ : 0 < φ) (hY : Y = 0)
    (heq : 2 * V * Y₁ + g * Y = 1) : 0 < φ * Y₁ - φ₁ * Y := by
  have hY₁ := variation_derivative_pos_at_zero hV hY heq
  simpa [hY] using mul_pos hφ hY₁

/-- Positivity of the manuscript's actual bracket expression follows from
the regular first variation, positive auxiliary coefficient, and simple
turns. No positivity assumption on the bracket is used. -/
theorem positive_bracket_of_regular_variation
    {V g g₁ φ φ₁ φ₂ Y Y₁ Y₂ : ℝ → ℝ} {s : Set ℝ} {a b : ℝ}
    (hab : a < b) (hs : IsOpen s) (hsub : Icc a b ⊆ s)
    (hV : ∀ x ∈ s, HasDerivAt V (-g x) x)
    (hg : ∀ x ∈ s, HasDerivAt g (g₁ x) x)
    (hφ : ∀ x ∈ s, HasDerivAt φ (φ₁ x) x)
    (hφ₁ : ∀ x ∈ s, HasDerivAt φ₁ (φ₂ x) x)
    (hY : ∀ x ∈ s, HasDerivAt Y (Y₁ x) x)
    (hY₁ : ∀ x ∈ s, HasDerivAt Y₁ (Y₂ x) x)
    (heq : ∀ x ∈ s, 2 * V x * Y₁ x + g x * Y x = 1)
    (hVa : V a = 0) (hVb : V b = 0)
    (hga : g a < 0) (hgb : 0 < g b)
    (hVpos : ∀ x ∈ Ioo a b, 0 < V x)
    (hφpos : ∀ x ∈ Icc a b, 0 < φ x)
    (hHpos : ∀ x ∈ Icc a b, 0 < auxiliary V g g₁ φ φ₁ φ₂ x) :
    ∀ x ∈ Icc a b, 0 < bracket φ φ₁ Y Y₁ x := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hsecond : ∀ x ∈ s,
      2 * V x * Y₂ x - g x * Y₁ x + g₁ x * Y x = 0 := by
    intro x hx
    exact variation_second_equation hs hx (hV x hx) (hg x hx)
      (hY x hx) (hY₁ x hx) heq
  have hva := variation_value_at_turn hVa (ne_of_lt hga) (heq a (hsub ha))
  have hvb := variation_value_at_turn hVb (ne_of_gt hgb) (heq b (hsub hb))
  have hYa : Y a < 0 := by rw [hva]; exact one_div_neg.mpr hga
  have hYb : 0 < Y b := by rw [hvb]; exact one_div_pos.mpr hgb
  obtain ⟨c, hc, hcz, hleft, hright⟩ := variation_unique_zero_and_signs hab
    (fun x hx => hY x (hsub hx)) hVpos
    (fun x hx => heq x (hsub (Ioo_subset_Icc_self hx))) hYa hYb
  have hRder : ∀ x ∈ Icc a b, DifferentiableAt ℝ (bracket φ φ₁ Y Y₁) x := by
    intro x hx
    exact (hasDerivAt_bracket (hφ x (hsub hx)) (hφ₁ x (hsub hx))
      (hY x (hsub hx)) (hY₁ x (hsub hx))).differentiableAt
  have hRfirst : ∀ x ∈ Ioo a b,
      2 * V x * deriv (bracket φ φ₁ Y Y₁) x =
        g x * bracket φ φ₁ Y Y₁ x - auxiliary V g g₁ φ φ₁ φ₂ x * Y x := by
    intro x hx
    have hh := hsub (Ioo_subset_Icc_self hx)
    exact bracket_first_equation (hφ x hh) (hφ₁ x hh) (hY x hh) (hY₁ x hh)
      (hsecond x hh)
  have hRa : 0 < bracket φ φ₁ Y Y₁ a := by
    have hval := bracket_value_at_turn (φ := φ a) (φ₁ := φ₁ a) (φ₂ := φ₂ a)
      hVa (ne_of_lt hga) (heq a (hsub ha)) (hsecond a (hsub ha))
    unfold bracket
    rw [hval]
    exact div_pos (hHpos a ha) (sq_pos_of_ne_zero (ne_of_lt hga))
  have hRb : 0 < bracket φ φ₁ Y Y₁ b := by
    have hval := bracket_value_at_turn (φ := φ b) (φ₁ := φ₁ b) (φ₂ := φ₂ b)
      hVb (ne_of_gt hgb) (heq b (hsub hb)) (hsecond b (hsub hb))
    unfold bracket
    rw [hval]
    exact div_pos (hHpos b hb) (sq_pos_of_ne_zero (ne_of_gt hgb))
  have hRc : 0 < bracket φ φ₁ Y Y₁ c :=
    bracket_pos_at_variation_zero (hVpos c hc) (hφpos c (Ioo_subset_Icc_self hc))
      hcz (heq c (hsub (Ioo_subset_Icc_self hc)))
  exact bracket_positive_from_first_equation hc.1 hc.2 hRder hVpos hHpos
    hRfirst hleft hright hRa hRc hRb

/-- Differentiating the first bracket equation yields its second-order
equation, including the coefficient `3g` from `V'=-g`. -/
theorem bracket_second_equation
    {V g g₁ H H₁ Y Y₁ R R₁ R₂ : ℝ → ℝ} {s : Set ℝ} {x : ℝ}
    (hs : IsOpen s) (hx : x ∈ s)
    (hV : HasDerivAt V (-g x) x) (hg : HasDerivAt g (g₁ x) x)
    (hH : HasDerivAt H (H₁ x) x) (hY : HasDerivAt Y (Y₁ x) x)
    (hR : HasDerivAt R (R₁ x) x) (hR₁ : HasDerivAt R₁ (R₂ x) x)
    (heq : ∀ z ∈ s, 2 * V z * R₁ z = g z * R z - H z * Y z) :
    2 * V x * R₂ x - 3 * g x * R₁ x =
      g₁ x * R x - H₁ x * Y x - H x * Y₁ x := by
  have hd := ((hV.const_mul 2).mul hR₁).sub ((hg.mul hR).sub (hH.mul hY))
  have he : (fun z => 2 * V z * R₁ z - (g z * R z - H z * Y z)) =ᶠ[𝓝 x]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hs.mem_nhds hx] with z hz
    exact sub_eq_zero.mpr (heq z hz)
  have hzero := (hd.congr_of_eventuallyEq he.symm).unique (hasDerivAt_const x (0 : ℝ))
  nlinarith [hzero]

/-- Polynomial elimination of the variation from the two bracket equations.
This form remains meaningful at a turning point. -/
theorem bracket_elimination_algebra
    (V g g₁ H H₁ φ φ₁ φ₂ Y Y₁ R R₁ R₂ : ℝ)
    (hfirst : 2 * V * R₁ = g * R - H * Y)
    (hsecond : 2 * V * R₂ - 3 * g * R₁ = g₁ * R - H₁ * Y - H * Y₁)
    (hR : R = φ * Y₁ - φ₁ * Y)
    (hH : H = φ * g₁ - φ₁ * g + 2 * V * φ₂) :
    2 * V * φ * H * R₂ -
      (2 * V * φ₁ * H + 3 * g * φ * H + 2 * V * φ * H₁) * R₁ +
      (2 * V * φ₂ * H + φ * g * H₁) * R = 0 := by
  linear_combination φ * H * hsecond - (φ₁ * H + φ * H₁) * hfirst +
    H ^ 2 * hR - H * R * hH

/-- On the regular interior the division-free elimination gives the
manuscript's second-order scalar equation. -/
theorem bracket_elimination
    {V g g₁ H H₁ φ φ₁ φ₂ Y Y₁ R R₁ R₂ : ℝ}
    (hV : V ≠ 0) (hφ : φ ≠ 0) (hH0 : H ≠ 0)
    (hfirst : 2 * V * R₁ = g * R - H * Y)
    (hsecond : 2 * V * R₂ - 3 * g * R₁ = g₁ * R - H₁ * Y - H * Y₁)
    (hR : R = φ * Y₁ - φ₁ * Y)
    (hH : H = φ * g₁ - φ₁ * g + 2 * V * φ₂) :
    R₂ - (φ₁ / φ + 3 * g / (2 * V) + H₁ / H) * R₁ +
      (φ₂ / φ + g * H₁ / (2 * V * H)) * R = 0 := by
  have he := bracket_elimination_algebra V g g₁ H H₁ φ φ₁ φ₂ Y Y₁ R R₁ R₂
    hfirst hsecond hR hH
  field_simp [hV, hφ, hH0]
  linear_combination (2 * V * φ * H) * he

/-- The derivative of the regular bracket at a simple turn follows from
the differentiated bracket equation and the already determined jets. -/
theorem bracket_derivative_at_turn
    {V g g₁ H H₁ Y Y₁ R R₁ R₂ : ℝ}
    (hV : V = 0) (hg : g ≠ 0)
    (hY : Y = 1 / g) (hY₁ : Y₁ = g₁ / g ^ 2) (hR : R = H / g ^ 2)
    (heq : 2 * V * R₂ - 3 * g * R₁ = g₁ * R - H₁ * Y - H * Y₁) :
    R₁ = H₁ / (3 * g ^ 2) := by
  rw [hV, hY, hY₁, hR] at heq
  field_simp [hg] at heq ⊢
  apply mul_left_cancel₀ (pow_ne_zero 4 hg)
  nlinarith [heq]

/-- The normalized critical mode, expressed using a real power. For
positive `H` this is exactly `R / H^(1/3)`. -/
noncomputable def mode (R H : ℝ → ℝ) (x : ℝ) : ℝ :=
  R x * H x ^ (-(1 : ℝ) / 3)

theorem mode_eq_div {R H : ℝ → ℝ} {x : ℝ} (hH : 0 < H x) :
    mode R H x = R x / H x ^ ((1 : ℝ) / 3) := by
  unfold mode
  rw [neg_div, Real.rpow_neg hH.le]
  rfl

theorem mode_pos {R H : ℝ → ℝ} {x : ℝ} (hR : 0 < R x) (hH : 0 < H x) :
    0 < mode R H x :=
  mul_pos hR (Real.rpow_pos_of_pos hH _)

/-- The ordinary derivative of the actual normalized-mode function. -/
theorem hasDerivAt_mode {R H : ℝ → ℝ} {R₁ H₁ x : ℝ}
    (hR : HasDerivAt R R₁ x) (hH : HasDerivAt H H₁ x) (hHpos : 0 < H x) :
    HasDerivAt (mode R H)
      ((R₁ - R x * H₁ / (3 * H x)) * H x ^ (-(1 : ℝ) / 3)) x := by
  have hd := hR.mul (hH.rpow_const (p := -(1 : ℝ) / 3) (Or.inl (ne_of_gt hHpos)))
  unfold mode
  convert hd using 1
  rw [Real.rpow_sub_one (ne_of_gt hHpos)]
  field_simp
  ring

/-- The normalized mode satisfies the Neumann condition at each regular
turn. This is derived from its endpoint jets, not imposed as a boundary
assumption. -/
theorem mode_derivative_at_turn {R H : ℝ → ℝ} {R₁ H₁ g x : ℝ}
    (hR : HasDerivAt R R₁ x) (hH : HasDerivAt H H₁ x)
    (hHpos : 0 < H x) (hg : g ≠ 0)
    (hRval : R x = H x / g ^ 2) (hR₁ : R₁ = H₁ / (3 * g ^ 2)) :
    HasDerivAt (mode R H) 0 x := by
  convert hasDerivAt_mode hR hH hHpos using 1
  rw [hRval, hR₁]
  field_simp [hg, ne_of_gt hHpos]
  ring

/-- A vanishing differentiable function is `O(V)` near a simple zero of
the potential gap. Applied to the mode derivative, this is the regular
endpoint estimate needed in the flux calculation. -/
theorem isBigO_gap_of_zero {f V : ℝ → ℝ} {f₁ V₁ c : ℝ}
    (hf : HasDerivAt f f₁ c) (hV : HasDerivAt V V₁ c)
    (hf0 : f c = 0) (hV0 : V c = 0) (hV₁ : V₁ ≠ 0) :
    f =O[𝓝 c] V := by
  simpa [hf0, hV0] using hf.isBigO_sub.trans (hV.isBigO_sub_rev hV₁)

/-- Exact coefficient computation for the cube-root normalization. -/
theorem normalized_curvature_algebra
    {V H φ : ℝ} (g H₁ H₂ φ₁ φ₂ : ℝ)
    (hV : V ≠ 0) (hH : H ≠ 0) (hφ : φ ≠ 0) :
    H₂ / (3 * H) - 2 * H₁ ^ 2 / (9 * H ^ 2) -
        (φ₁ / φ + 3 * g / (2 * V) + H₁ / H) * H₁ / (3 * H) +
        φ₂ / φ + g * H₁ / (2 * V * H) =
      H₂ / (3 * H) - 5 * H₁ ^ 2 / (9 * H ^ 2) -
        φ₁ * H₁ / (3 * φ * H) + φ₂ / φ := by
  field_simp
  ring

/-- The boundary concomitant in the energy-dependent Green identity. -/
noncomputable def greenBoundary
    (p pL U U₁ d d₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  p x * (U x * d₁ x - U₁ x * d x) + U x * pL x * U₁ x

/-- The full Green density. The energy derivative of the curvature
coefficient is retained explicitly. -/
noncomputable def greenDensity
    (p pL Q QL U U₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  pL x * (U₁ x ^ 2 - Q x * U x ^ 2) - p x * QL x * U x ^ 2

/-- The two differential equations imply the Green identity by product
differentiation. Neither the boundary identity nor its integrand is an
assumption. -/
theorem hasDerivAt_greenBoundary
    {p p₁ pL pL₁ Q QL U U₁ U₂ d d₁ d₂ : ℝ → ℝ} {x : ℝ}
    (hp : HasDerivAt p (p₁ x) x) (hpL : HasDerivAt pL (pL₁ x) x)
    (hU : HasDerivAt U (U₁ x) x) (hU₁ : HasDerivAt U₁ (U₂ x) x)
    (hd : HasDerivAt d (d₁ x) x) (hd₁ : HasDerivAt d₁ (d₂ x) x)
    (hbase : p x * U₂ x + p₁ x * U₁ x + p x * Q x * U x = 0)
    (hvariation : p x * d₂ x + p₁ x * d₁ x + p x * Q x * d x =
      -pL x * U₂ x - pL₁ x * U₁ x - (pL x * Q x + p x * QL x) * U x) :
    HasDerivAt (greenBoundary p pL U U₁ d d₁)
      (greenDensity p pL Q QL U U₁ x) x := by
  unfold greenBoundary greenDensity
  convert (hp.mul ((hU.mul hd₁).sub (hU₁.mul hd))).add
    ((hU.mul hpL).mul hU₁) using 1
  linear_combination (-U x) * hvariation + d x * hbase

/-- The Green density is integrable on every compact regular interval;
continuity of the coefficients discharges the integrability obligation. -/
theorem greenDensity_intervalIntegrable
    {p pL Q QL U U₁ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hp : ContinuousOn p (Icc a b)) (hpL : ContinuousOn pL (Icc a b))
    (hQ : ContinuousOn Q (Icc a b)) (hQL : ContinuousOn QL (Icc a b))
    (hU : ContinuousOn U (Icc a b)) (hU₁ : ContinuousOn U₁ (Icc a b)) :
    IntervalIntegrable (greenDensity p pL Q QL U U₁) MeasureTheory.volume a b := by
  exact ((hpL.mul ((hU₁.pow 2).sub (hQ.mul (hU.pow 2)))).sub
    ((hp.mul hQL).mul (hU.pow 2))).intervalIntegrable_of_Icc hab

/-- Integration of the proved Green derivative gives the complete
finite-interval identity, including the `Q_L` term. All integrability
hypotheses are discharged from coefficient continuity. -/
theorem green_identity_on_Icc
    {p p₁ pL pL₁ Q QL U U₁ U₂ d d₁ d₂ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p₁ x) x)
    (hpL : ∀ x ∈ Icc a b, HasDerivAt pL (pL₁ x) x)
    (hU : ∀ x ∈ Icc a b, HasDerivAt U (U₁ x) x)
    (hU₁ : ∀ x ∈ Icc a b, HasDerivAt U₁ (U₂ x) x)
    (hd : ∀ x ∈ Icc a b, HasDerivAt d (d₁ x) x)
    (hd₁ : ∀ x ∈ Icc a b, HasDerivAt d₁ (d₂ x) x)
    (hQ : ContinuousOn Q (Icc a b)) (hQL : ContinuousOn QL (Icc a b))
    (hbase : ∀ x ∈ Ioo a b,
      p x * U₂ x + p₁ x * U₁ x + p x * Q x * U x = 0)
    (hvariation : ∀ x ∈ Ioo a b,
      p x * d₂ x + p₁ x * d₁ x + p x * Q x * d x =
        -pL x * U₂ x - pL₁ x * U₁ x - (pL x * Q x + p x * QL x) * U x) :
    (∫ x in a..b, greenDensity p pL Q QL U U₁ x) =
      greenBoundary p pL U U₁ d d₁ b - greenBoundary p pL U U₁ d d₁ a := by
  have hpc : ContinuousOn p (Icc a b) := fun x hx =>
    (hp x hx).continuousAt.continuousWithinAt
  have hpLc : ContinuousOn pL (Icc a b) := fun x hx =>
    (hpL x hx).continuousAt.continuousWithinAt
  have hUc : ContinuousOn U (Icc a b) := fun x hx =>
    (hU x hx).continuousAt.continuousWithinAt
  have hU₁c : ContinuousOn U₁ (Icc a b) := fun x hx =>
    (hU₁ x hx).continuousAt.continuousWithinAt
  have hdc : ContinuousOn d (Icc a b) := fun x hx =>
    (hd x hx).continuousAt.continuousWithinAt
  have hd₁c : ContinuousOn d₁ (Icc a b) := fun x hx =>
    (hd₁ x hx).continuousAt.continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    ((hpc.mul ((hUc.mul hd₁c).sub (hU₁c.mul hdc))).add ((hUc.mul hpLc).mul hU₁c))
  · intro x hx
    have hm := Ioo_subset_Icc_self hx
    exact hasDerivAt_greenBoundary (hp x hm) (hpL x hm) (hU x hm) (hU₁ x hm)
      (hd x hm) (hd₁ x hm) (hbase x hx) (hvariation x hx)
  · exact greenDensity_intervalIntegrable hab hpc hpLc hQ hQL hUc hU₁c

/-- Explicit first derivative of the cube-root-normalized mode. -/
noncomputable def modePrime (R R₁ H H₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (R₁ x - R x * H₁ x / (3 * H x)) * H x ^ (-(1 : ℝ) / 3)

/-- The second derivative of the normalized mode is computed from the
ordinary first and second jets of `R` and `H`. -/
theorem hasDerivAt_modePrime
    {R R₁ H H₁ : ℝ → ℝ} {R₂ H₂ x : ℝ}
    (hR : HasDerivAt R (R₁ x) x) (hR₁ : HasDerivAt R₁ R₂ x)
    (hH : HasDerivAt H (H₁ x) x) (hH₁ : HasDerivAt H₁ H₂ x)
    (hHpos : 0 < H x) :
    HasDerivAt (modePrime R R₁ H H₁)
      ((R₂ - 2 * H₁ x / (3 * H x) * R₁ x +
        (4 * H₁ x ^ 2 / (9 * H x ^ 2) - H₂ / (3 * H x)) * R x) *
        H x ^ (-(1 : ℝ) / 3)) x := by
  have hden : 3 * H x ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hHpos)
  have hd := (hR₁.sub ((hR.mul hH₁).div (hH.const_mul 3) hden)).mul
    (hH.rpow_const (p := -(1 : ℝ) / 3) (Or.inl (ne_of_gt hHpos)))
  unfold modePrime
  convert hd using 1
  rw [Real.rpow_sub_one (ne_of_gt hHpos)]
  field_simp
  ring

/-- Curvature coefficient in the normalized Sturm equation. -/
noncomputable def curvature (H H₁ H₂ φ φ₁ φ₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  H₂ x / (3 * H x) - 5 * H₁ x ^ 2 / (9 * H x ^ 2) -
    φ₁ x * H₁ x / (3 * φ x * H x) + φ₂ x / φ x

/-- Exact gauge-transformation residual, before invoking a differential
equation. The factor `s` will be the real power `H^(-1/3)`. -/
theorem normalization_residual_algebra
    {V H φ : ℝ} (g H₁ H₂ φ₁ φ₂ R R₁ R₂ s : ℝ)
    (hV : V ≠ 0) (hH : H ≠ 0) (hφ : φ ≠ 0) :
    (R₂ - 2 * H₁ / (3 * H) * R₁ +
        (4 * H₁ ^ 2 / (9 * H ^ 2) - H₂ / (3 * H)) * R) * s -
      (φ₁ / φ + 3 * g / (2 * V) + H₁ / (3 * H)) *
        ((R₁ - R * H₁ / (3 * H)) * s) +
      (H₂ / (3 * H) - 5 * H₁ ^ 2 / (9 * H ^ 2) -
        φ₁ * H₁ / (3 * φ * H) + φ₂ / φ) * (R * s) =
      (R₂ - (φ₁ / φ + 3 * g / (2 * V) + H₁ / H) * R₁ +
        (φ₂ / φ + g * H₁ / (2 * V * H)) * R) * s := by
  field_simp
  ring

/-- The computed derivative of the mode derivative satisfies the
normalized equation whenever the bracket satisfies its eliminated
equation. This supplies the actual function-level gauge transformation. -/
theorem hasDerivAt_modePrime_of_bracket_equation
    {V g R R₁ H H₁ H₂ φ φ₁ φ₂ : ℝ → ℝ} {R₂ x : ℝ}
    (hR : HasDerivAt R (R₁ x) x) (hR₁ : HasDerivAt R₁ R₂ x)
    (hH : HasDerivAt H (H₁ x) x) (hH₁ : HasDerivAt H₁ (H₂ x) x)
    (hV : V x ≠ 0) (hHpos : 0 < H x) (hφ : φ x ≠ 0)
    (heq : R₂ - (φ₁ x / φ x + 3 * g x / (2 * V x) + H₁ x / H x) * R₁ x +
      (φ₂ x / φ x + g x * H₁ x / (2 * V x * H x)) * R x = 0) :
    HasDerivAt (modePrime R R₁ H H₁)
      ((φ₁ x / φ x + 3 * g x / (2 * V x) + H₁ x / (3 * H x)) *
        modePrime R R₁ H H₁ x - curvature H H₁ H₂ φ φ₁ φ₂ x * mode R H x) x := by
  have halg := normalization_residual_algebra (g x) (H₁ x) (H₂ x) (φ₁ x) (φ₂ x)
    (R x) (R₁ x) R₂ (H x ^ (-(1 : ℝ) / 3)) hV (ne_of_gt hHpos) hφ
  rw [heq, zero_mul] at halg
  convert hasDerivAt_modePrime hR hR₁ hH hH₁ hHpos using 1
  unfold modePrime mode curvature
  linarith [halg]

/-- The positive Sturm weight, in a power-product form equivalent to
`V^(3/2)/(φ H^(1/3))`. -/
noncomputable def weight (V φ H : ℝ → ℝ) (x : ℝ) : ℝ :=
  V x ^ ((3 : ℝ) / 2) * H x ^ (-(1 : ℝ) / 3) / φ x

theorem weight_eq_div {V φ H : ℝ → ℝ} {x : ℝ} (hH : 0 < H x) :
    weight V φ H x = V x ^ ((3 : ℝ) / 2) / (φ x * H x ^ ((1 : ℝ) / 3)) := by
  unfold weight
  rw [neg_div, Real.rpow_neg hH.le]
  ring

theorem weight_pos {V φ H : ℝ → ℝ} {x : ℝ}
    (hV : 0 < V x) (hφ : 0 < φ x) (hH : 0 < H x) :
    0 < weight V φ H x :=
  div_pos (mul_pos (Real.rpow_pos_of_pos hV _) (Real.rpow_pos_of_pos hH _)) hφ

/-- The logarithmic derivative of the actual Sturm weight. -/
theorem hasDerivAt_weight {V φ H : ℝ → ℝ} {g φ₁ H₁ x : ℝ}
    (hV : HasDerivAt V (-g) x) (hφ : HasDerivAt φ φ₁ x) (hH : HasDerivAt H H₁ x)
    (hVpos : 0 < V x) (hφ0 : φ x ≠ 0) (hHpos : 0 < H x) :
    HasDerivAt (weight V φ H)
      (-(φ₁ / φ x + 3 * g / (2 * V x) + H₁ / (3 * H x)) * weight V φ H x) x := by
  have hd := ((hV.rpow_const (p := (3 : ℝ) / 2) (Or.inl (ne_of_gt hVpos))).mul
    (hH.rpow_const (p := -(1 : ℝ) / 3) (Or.inl (ne_of_gt hHpos)))).div hφ hφ0
  unfold weight
  convert hd using 1
  rw [Real.rpow_sub_one (ne_of_gt hVpos), Real.rpow_sub_one (ne_of_gt hHpos)]
  field_simp
  ring

/-- The normalized critical mode satisfies the actual self-adjoint
differential equation `(p U')' = -p Q U` on the regular interior. -/
theorem normalized_mode_sturm_equation
    {V g R R₁ H H₁ H₂ φ φ₁ φ₂ : ℝ → ℝ} {R₂ x : ℝ}
    (hV : HasDerivAt V (-g x) x) (hφ : HasDerivAt φ (φ₁ x) x)
    (hR : HasDerivAt R (R₁ x) x) (hR₁ : HasDerivAt R₁ R₂ x)
    (hH : HasDerivAt H (H₁ x) x) (hH₁ : HasDerivAt H₁ (H₂ x) x)
    (hVpos : 0 < V x) (hHpos : 0 < H x) (hφ0 : φ x ≠ 0)
    (heq : R₂ - (φ₁ x / φ x + 3 * g x / (2 * V x) + H₁ x / H x) * R₁ x +
      (φ₂ x / φ x + g x * H₁ x / (2 * V x * H x)) * R x = 0) :
    HasDerivAt (fun z => weight V φ H z * modePrime R R₁ H H₁ z)
      (-weight V φ H x * curvature H H₁ H₂ φ φ₁ φ₂ x * mode R H x) x := by
  have hp := hasDerivAt_weight hV hφ hH hVpos hφ0 hHpos
  have hU₁ := hasDerivAt_modePrime_of_bracket_equation
    hR hR₁ hH hH₁ (ne_of_gt hVpos) hHpos hφ0 heq
  convert hp.mul hU₁ using 1
  ring

/-- The actual weighted flux has order `V^(5/2)` whenever the regular
mode derivative has order `V`. Positivity of the gap is only required
along the approach filter, so this covers both one-sided turning limits. -/
theorem weight_flux_isBigO
    {V φ H f : ℝ → ℝ} {c : ℝ} {l : Filter ℝ}
    (hl : l ≤ 𝓝 c) (hφ : ContinuousAt φ c) (hH : ContinuousAt H c)
    (hφ0 : φ c ≠ 0) (hHpos : 0 < H c)
    (hVnonneg : ∀ᶠ x in l, 0 ≤ V x) (hf : f =O[l] V) :
    (fun x => weight V φ H x * f x) =O[l] (fun x => V x ^ ((5 : ℝ) / 2)) := by
  have hα : ContinuousAt (fun x => H x ^ (-(1 : ℝ) / 3) / φ x) c :=
    (hH.rpow_const (Or.inl (ne_of_gt hHpos))).div hφ hφ0
  have hαO : (fun x => H x ^ (-(1 : ℝ) / 3) / φ x) =O[l] (fun _ => (1 : ℝ)) :=
    isBigO_const_of_tendsto (hα.tendsto.mono_left hl) one_ne_zero
  have hh := ((isBigO_refl (fun x => V x ^ ((3 : ℝ) / 2)) l).mul hf).mul hαO
  apply hh.congr' ?_ ?_
  · filter_upwards [] with x
    unfold weight
    ring
  · filter_upwards [hVnonneg] with x hx
    simp only [mul_one]
    rw [← Real.rpow_add_one' hx (by norm_num : (3 : ℝ) / 2 + 1 ≠ 0)]
    norm_num

/-- A differentiable vanishing mode derivative at a simple gap zero gives
the full `V^(5/2)` flux estimate; no flux bound is assumed. -/
theorem weight_flux_isBigO_at_simple_turn
    {V φ H f : ℝ → ℝ} {c V₁ f₁ : ℝ} {l : Filter ℝ}
    (hl : l ≤ 𝓝 c) (hφ : ContinuousAt φ c) (hH : ContinuousAt H c)
    (hφ0 : φ c ≠ 0) (hHpos : 0 < H c)
    (hVnonneg : ∀ᶠ x in l, 0 ≤ V x)
    (hf : HasDerivAt f f₁ c) (hV : HasDerivAt V V₁ c)
    (hf0 : f c = 0) (hV0 : V c = 0) (hV₁ : V₁ ≠ 0) :
    (fun x => weight V φ H x * f x) =O[l] (fun x => V x ^ ((5 : ℝ) / 2)) :=
  weight_flux_isBigO hl hφ hH hφ0 hHpos hVnonneg
    ((isBigO_gap_of_zero hf hV hf0 hV0 hV₁).mono hl)

/-- For the actual normalized-mode formula, the endpoint jets imply both
the `V^(5/2)` flux estimate and zero limiting flux. -/
theorem mode_flux_at_simple_turn
    {V φ R R₁ H H₁ : ℝ → ℝ} {c g R₂ H₂ : ℝ} {l : Filter ℝ}
    (hl : l ≤ 𝓝 c) (hφ : ContinuousAt φ c) (hφ0 : φ c ≠ 0)
    (hV : HasDerivAt V (-g) c) (hV0 : V c = 0) (hg : g ≠ 0)
    (hR : HasDerivAt R (R₁ c) c) (hR₁ : HasDerivAt R₁ R₂ c)
    (hH : HasDerivAt H (H₁ c) c) (hH₁ : HasDerivAt H₁ H₂ c) (hHpos : 0 < H c)
    (hRval : R c = H c / g ^ 2) (hR₁val : R₁ c = H₁ c / (3 * g ^ 2))
    (hVnonneg : ∀ᶠ x in l, 0 ≤ V x) :
    ((fun x => weight V φ H x * modePrime R R₁ H H₁ x) =O[l]
      (fun x => V x ^ ((5 : ℝ) / 2))) ∧
    Tendsto (fun x => weight V φ H x * modePrime R R₁ H H₁ x) l (𝓝 0) := by
  have hzero : modePrime R R₁ H H₁ c = 0 :=
    (hasDerivAt_mode hR hH hHpos).unique
      (mode_derivative_at_turn hR hH hHpos hg hRval hR₁val)
  have hbig := weight_flux_isBigO_at_simple_turn hl hφ hH.continuousAt hφ0 hHpos
    hVnonneg (hasDerivAt_modePrime hR hR₁ hH hH₁ hHpos) hV hzero hV0 (neg_ne_zero.mpr hg)
  refine ⟨hbig, hbig.trans_tendsto ?_⟩
  have hc := (hV.continuousAt.rpow_const
    (p := (5 : ℝ) / 2) (Or.inr (by norm_num))).tendsto.mono_left hl
  simpa [hV0] using hc

end LeanVerification.CriticalMode
