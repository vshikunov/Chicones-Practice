import LeanVerification.PeriodicReflection

/-!
# Exact reflected-time values on the periodic phase path

The endpoint identities are included, so reflected time zero and a complete
period both have the correct zero-momentum state.
-/

noncomputable section

open Set

namespace LeanVerification.PeriodicReflection

open LeanVerification.ReflectionArc

theorem periodicX_at_reflected_time (X : ℝ → ℝ) (q : ℝ) (hq : 0 < q)
    {s : ℝ} (hs : s ∈ Icc 0 q) :
    periodicX X q hq (2 * q - s) = X s := by
  have ht : 2 * q - s ∈ Icc 0 (2 * q) := by
    constructor <;> linarith [hs.1, hs.2]
  change periodicExtension (2 * q) (by linarith) (reflectedX X q) (2 * q - s) = X s
  rw [periodicExtension_eq_on _ _ _ (reflectedX_endpoints hq) ht,
    reflectedX_eq_on_right (by linarith [hs.2] : q ≤ 2 * q - s), sub_sub_cancel]

theorem periodicY_at_reflected_time (Y : ℝ → ℝ) (q : ℝ) (hq : 0 < q)
    (hY0 : Y 0 = 0) (hYq : Y q = 0) {s : ℝ} (hs : s ∈ Icc 0 q) :
    periodicY Y q hq (2 * q - s) = -Y s := by
  have ht : 2 * q - s ∈ Icc 0 (2 * q) := by
    constructor <;> linarith [hs.1, hs.2]
  change periodicExtension (2 * q) (by linarith) (reflectedY Y q) (2 * q - s) = -Y s
  rw [periodicExtension_eq_on _ _ _ (reflectedY_endpoints hq hY0) ht,
    reflectedY_eq_on_right (by linarith [hs.2] : q ≤ 2 * q - s) hYq, sub_sub_cancel]

end LeanVerification.PeriodicReflection
