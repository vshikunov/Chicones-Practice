import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Linarith

/-!
# Reflecting a mechanical arc at a turning point

A solution of `X' = Y`, `Y' = A(X)` on `[0,q]` with zero endpoint
velocities extends to `[0,2q]` by reversing position time and momentum sign.
The within derivatives glue at `q`, and both endpoint values and derivatives
match for subsequent periodic continuation. No regularity of `A` is assumed
beyond the given differential equations.
-/

noncomputable section

namespace LeanVerification.ReflectionArc

open Set Filter
open scoped Topology

def reflectedX (X : ℝ → ℝ) (q t : ℝ) : ℝ :=
  if t ≤ q then X t else X (2 * q - t)

def reflectedY (Y : ℝ → ℝ) (q t : ℝ) : ℝ :=
  if t ≤ q then Y t else -Y (2 * q - t)

theorem reflectedX_eq_on_left {X : ℝ → ℝ} {q t : ℝ} (ht : t ≤ q) :
    reflectedX X q t = X t := by
  simp [reflectedX, ht]

theorem reflectedY_eq_on_left {Y : ℝ → ℝ} {q t : ℝ} (ht : t ≤ q) :
    reflectedY Y q t = Y t := by
  simp [reflectedY, ht]

theorem reflectedX_eq_on_right {X : ℝ → ℝ} {q t : ℝ} (ht : q ≤ t) :
    reflectedX X q t = X (2 * q - t) := by
  by_cases h : t ≤ q
  · have heq : t = q := le_antisymm h ht
    subst t
    simp [reflectedX, two_mul]
  · simp [reflectedX, h]

theorem reflectedY_eq_on_right {Y : ℝ → ℝ} {q t : ℝ}
    (ht : q ≤ t) (hYq : Y q = 0) :
    reflectedY Y q t = -Y (2 * q - t) := by
  by_cases h : t ≤ q
  · have heq : t = q := le_antisymm h ht
    subst t
    simp [reflectedY, two_mul, hYq]
  · simp [reflectedY, h]

theorem reflectedX_zero {X : ℝ → ℝ} {q : ℝ} (hq : 0 < q) :
    reflectedX X q 0 = X 0 :=
  reflectedX_eq_on_left hq.le

theorem reflectedY_zero {Y : ℝ → ℝ} {q : ℝ} (hq : 0 < q) :
    reflectedY Y q 0 = Y 0 :=
  reflectedY_eq_on_left hq.le

theorem reflectedX_two_mul {X : ℝ → ℝ} {q : ℝ} (hq : 0 < q) :
    reflectedX X q (2 * q) = X 0 := by
  rw [reflectedX_eq_on_right (by linarith : q ≤ 2 * q), sub_self]

theorem reflectedY_two_mul {Y : ℝ → ℝ} {q : ℝ} (hq : 0 < q) :
    reflectedY Y q (2 * q) = -Y 0 := by
  simp [reflectedY, show ¬2 * q ≤ q by linarith]

theorem reflectedX_endpoints {X : ℝ → ℝ} {q : ℝ} (hq : 0 < q) :
    reflectedX X q 0 = reflectedX X q (2 * q) := by
  rw [reflectedX_zero hq, reflectedX_two_mul hq]

theorem reflectedY_endpoints {Y : ℝ → ℝ} {q : ℝ}
    (hq : 0 < q) (hY0 : Y 0 = 0) :
    reflectedY Y q 0 = reflectedY Y q (2 * q) := by
  rw [reflectedY_zero hq, reflectedY_two_mul hq, hY0, neg_zero]

private theorem hasDerivWithinAt_glue_Icc {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    {f f' : ℝ → ℝ}
    (hl : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t)
    (hr : ∀ t ∈ Icc b c, HasDerivWithinAt f (f' t) (Icc b c) t) :
    ∀ t ∈ Icc a c, HasDerivWithinAt f (f' t) (Icc a c) t := by
  intro t ht
  rcases lt_trichotomy t b with hlt | heq | hgt
  · apply (hl t ⟨ht.1, hlt.le⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with s hs hsb
    exact ⟨hs.1, hsb.le⟩
  · subst t
    simpa only [Icc_union_Icc_eq_Icc hab hbc] using
      (hl b ⟨hab, le_rfl⟩).union (hr b ⟨le_rfl, hbc⟩)
  · apply (hr t ⟨hgt.le, ht.2⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hgt)] with s hs hbs
    exact ⟨hbs.le, hs.2⟩

private theorem mapsTo_reflection {q : ℝ} :
    MapsTo (fun t : ℝ => 2 * q - t) (Icc q (2 * q)) (Icc 0 q) := by
  intro t ht
  change 0 ≤ 2 * q - t ∧ 2 * q - t ≤ q
  constructor <;> linarith [ht.1, ht.2]

/-- Time reflection and momentum reversal preserve the position equation,
including the turning point at `q`. -/
theorem hasDerivWithinAt_reflectedX {X Y : ℝ → ℝ} {q : ℝ}
    (hq : 0 < q) (hYq : Y q = 0)
    (hX : ∀ t ∈ Icc 0 q, HasDerivWithinAt X (Y t) (Icc 0 q) t) :
    ∀ t ∈ Icc 0 (2 * q),
      HasDerivWithinAt (reflectedX X q) (reflectedY Y q t) (Icc 0 (2 * q)) t := by
  apply hasDerivWithinAt_glue_Icc hq.le (by linarith : q ≤ 2 * q)
  · intro t ht
    rw [reflectedY_eq_on_left ht.2]
    exact (hX t ht).congr_of_mem
      (fun s hs => reflectedX_eq_on_left hs.2) ht
  · intro t ht
    rw [reflectedY_eq_on_right ht.1 hYq]
    have hd : HasDerivWithinAt (fun s => X (2 * q - s)) (-Y (2 * q - t))
        (Icc q (2 * q)) t := by
      simpa only [Function.comp_def, mul_neg_one] using
        (hX (2 * q - t) (mapsTo_reflection ht)).comp t
          ((hasDerivAt_id t).const_sub (2 * q)).hasDerivWithinAt mapsTo_reflection
    exact hd.congr_of_mem (fun s hs => reflectedX_eq_on_right hs.1) ht

/-- The two sign reversals cancel in the acceleration equation. -/
theorem hasDerivWithinAt_reflectedY {X Y A : ℝ → ℝ} {q : ℝ}
    (hq : 0 < q) (hYq : Y q = 0)
    (hY : ∀ t ∈ Icc 0 q, HasDerivWithinAt Y (A (X t)) (Icc 0 q) t) :
    ∀ t ∈ Icc 0 (2 * q),
      HasDerivWithinAt (reflectedY Y q) (A (reflectedX X q t))
        (Icc 0 (2 * q)) t := by
  apply hasDerivWithinAt_glue_Icc hq.le (by linarith : q ≤ 2 * q)
  · intro t ht
    rw [reflectedX_eq_on_left ht.2]
    exact (hY t ht).congr_of_mem
      (fun s hs => reflectedY_eq_on_left hs.2) ht
  · intro t ht
    rw [reflectedX_eq_on_right ht.1]
    have hd : HasDerivWithinAt (fun s => -Y (2 * q - s)) (A (X (2 * q - t)))
        (Icc q (2 * q)) t := by
      simpa only [Function.comp_def, mul_neg_one, neg_neg] using
        ((hY (2 * q - t) (mapsTo_reflection ht)).comp t
          ((hasDerivAt_id t).const_sub (2 * q)).hasDerivWithinAt mapsTo_reflection).neg
    exact hd.congr_of_mem (fun s hs => reflectedY_eq_on_right hs.1 hYq) ht

/-- Strict increase on the original arc prevents a return to its initial
position at any time strictly between `0` and `2q`. -/
theorem reflectedX_gt_initial {X : ℝ → ℝ} {q t : ℝ}
    (hq : 0 < q) (hX : StrictMonoOn X (Icc 0 q)) (ht : t ∈ Ioo 0 (2 * q)) :
    X 0 < reflectedX X q t := by
  by_cases htq : t ≤ q
  · rw [reflectedX_eq_on_left htq]
    exact hX ⟨le_rfl, hq.le⟩ ⟨ht.1.le, htq⟩ ht.1
  · rw [reflectedX_eq_on_right (le_of_not_ge htq)]
    apply hX ⟨le_rfl, hq.le⟩
    · constructor <;> linarith [ht.2]
    · linarith [ht.2]

end LeanVerification.ReflectionArc
