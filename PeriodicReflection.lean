import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Tactic.Linarith
import LeanVerification.ReflectionArc

/-!
# Reflection of a mechanical arc and periodic continuation

The construction starts with a genuine solution on a closed time interval,
including the one-sided differential equations at its endpoints. Reflection
reverses position time and momentum sign. Matching endpoint values and
derivatives justify the periodic extension at every join.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace LeanVerification.PeriodicReflection

open LeanVerification.ReflectionArc

/-- Extend a function from `[0,p]` with period `p`. -/
def periodicExtension (p : ℝ) (hp : 0 < p) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f (toIcoMod hp 0 t)

theorem periodic_periodicExtension (p : ℝ) (hp : 0 < p) (f : ℝ → ℝ) :
    Function.Periodic (periodicExtension p hp f) p := by
  intro t
  simp only [periodicExtension, toIcoMod_add_right]

theorem periodicExtension_eq_on (p : ℝ) (hp : 0 < p) (f : ℝ → ℝ)
    (hend : f 0 = f p) :
    EqOn (periodicExtension p hp f) f (Icc 0 p) := by
  intro t ht
  rcases lt_or_eq_of_le ht.2 with hlt | heqt
  · unfold periodicExtension
    rw [(toIcoMod_eq_self hp).2 (by simpa only [zero_add] using ⟨ht.1, hlt⟩)]
  · subst t
    have hmod : toIcoMod hp 0 p = 0 := by
      simpa only [zero_add] using toIcoMod_apply_right hp (0 : ℝ)
    simpa only [periodicExtension, hmod] using hend

/-- Matching one-sided derivatives make a periodic extension differentiable,
including at the integer multiples of its period. -/
theorem hasDerivAt_periodicExtension (p : ℝ) (hp : 0 < p) (f f' : ℝ → ℝ)
    (hf : ∀ t ∈ Icc 0 p, HasDerivWithinAt f (f' t) (Icc 0 p) t)
    (hend : f 0 = f p) (hderiv : f' 0 = f' p) (t : ℝ) :
    HasDerivAt (periodicExtension p hp f) (f' (toIcoMod hp 0 t)) t := by
  have heq := periodicExtension_eq_on p hp f hend
  have hperiod := periodic_periodicExtension p hp f
  have hzero : HasDerivAt (periodicExtension p hp f) (f' 0) 0 := by
    have hright : HasDerivWithinAt (periodicExtension p hp f) (f' 0) (Icc 0 p) 0 :=
      (hf 0 ⟨le_rfl, hp.le⟩).congr_of_mem heq ⟨le_rfl, hp.le⟩
    have hmaps : MapsTo (fun s : ℝ => s + p) (Icc (-p) 0) (Icc 0 p) := by
      intro s hs
      change 0 ≤ s + p ∧ s + p ≤ p
      constructor <;> linarith [hs.1, hs.2]
    have hleft₀ : HasDerivWithinAt (fun s : ℝ => f (s + p)) (f' p)
        (Icc (-p) 0) 0 := by
      simpa only [Function.comp_def, mul_one] using
        (hf p ⟨hp.le, le_rfl⟩).comp_of_eq 0
          ((hasDerivAt_id (0 : ℝ)).add_const p).hasDerivWithinAt hmaps (by simp)
    have hleft : HasDerivWithinAt (periodicExtension p hp f) (f' 0)
        (Icc (-p) 0) 0 := by
      apply (hleft₀.congr_deriv hderiv.symm).congr_of_mem
      · intro s hs
        exact (hperiod s).symm.trans (heq (hmaps hs))
      · exact ⟨by linarith, le_rfl⟩
    have hunion := hleft.union hright
    rw [Icc_union_Icc_eq_Icc (by linarith : -p ≤ (0 : ℝ)) hp.le] at hunion
    exact hunion.hasDerivAt (Icc_mem_nhds (by linarith) hp)
  have hbase : ∀ s ∈ Ico 0 p,
      HasDerivAt (periodicExtension p hp f) (f' s) s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with hzero' | hpos
    · simpa only [← hzero'] using hzero
    · exact ((hf s ⟨hs.1, hs.2.le⟩).congr_of_mem heq ⟨hs.1, hs.2.le⟩).hasDerivAt
        (Icc_mem_nhds hpos hs.2)
  have hd := hbase (toIcoMod hp 0 t) (toIcoMod_mem_Ico' hp t)
  have hshift := hd.comp_of_eq t
    ((hasDerivAt_id t).sub_const (toIcoDiv hp 0 t • p))
    (self_sub_toIcoDiv_zsmul hp 0 t).symm
  simpa only [Function.comp_def, mul_one, hperiod.sub_zsmul_eq] using hshift

/-- Position of the reflected and periodically continued arc. -/
def periodicX (X : ℝ → ℝ) (q : ℝ) (hq : 0 < q) : ℝ → ℝ :=
  periodicExtension (2 * q) (by linarith) (reflectedX X q)

/-- Velocity of the reflected and periodically continued arc. -/
def periodicY (Y : ℝ → ℝ) (q : ℝ) (hq : 0 < q) : ℝ → ℝ :=
  periodicExtension (2 * q) (by linarith) (reflectedY Y q)

theorem periodicX_eq_on (X : ℝ → ℝ) (q : ℝ) (hq : 0 < q) :
    EqOn (periodicX X q hq) X (Icc 0 q) := by
  intro t ht
  have hm : toIcoMod (by linarith : 0 < 2 * q) 0 t = t := by
    apply (toIcoMod_eq_self _).2
    change 0 ≤ t ∧ t < 0 + 2 * q
    exact ⟨ht.1, by linarith [ht.2]⟩
  simpa only [periodicX, periodicExtension, hm] using reflectedX_eq_on_left ht.2

theorem periodicY_eq_on (Y : ℝ → ℝ) (q : ℝ) (hq : 0 < q) :
    EqOn (periodicY Y q hq) Y (Icc 0 q) := by
  intro t ht
  have hm : toIcoMod (by linarith : 0 < 2 * q) 0 t = t := by
    apply (toIcoMod_eq_self _).2
    change 0 ≤ t ∧ t < 0 + 2 * q
    exact ⟨ht.1, by linarith [ht.2]⟩
  simpa only [periodicY, periodicExtension, hm] using reflectedY_eq_on_left ht.2

@[simp] theorem periodicX_zero (X : ℝ → ℝ) (q : ℝ) (hq : 0 < q) :
    periodicX X q hq 0 = X 0 :=
  periodicX_eq_on X q hq ⟨le_rfl, hq.le⟩

@[simp] theorem periodicY_zero (Y : ℝ → ℝ) (q : ℝ) (hq : 0 < q) :
    periodicY Y q hq 0 = Y 0 :=
  periodicY_eq_on Y q hq ⟨le_rfl, hq.le⟩

theorem periodic_periodicX (X : ℝ → ℝ) (q : ℝ) (hq : 0 < q) :
    Function.Periodic (periodicX X q hq) (2 * q) :=
  periodic_periodicExtension _ _ _

theorem periodic_periodicY (Y : ℝ → ℝ) (q : ℝ) (hq : 0 < q) :
    Function.Periodic (periodicY Y q hq) (2 * q) :=
  periodic_periodicExtension _ _ _

theorem periodic_phase (X Y : ℝ → ℝ) (q : ℝ) (hq : 0 < q) :
    Function.Periodic (fun t => (periodicX X q hq t, periodicY Y q hq t)) (2 * q) := by
  intro t
  exact Prod.ext (periodic_periodicX X q hq t) (periodic_periodicY Y q hq t)

/-- The position equation holds at every real time, including all joins. -/
theorem hasDerivAt_periodicX {X Y : ℝ → ℝ} {q : ℝ}
    (hq : 0 < q) (hY0 : Y 0 = 0) (hYq : Y q = 0)
    (hX : ∀ t ∈ Icc 0 q, HasDerivWithinAt X (Y t) (Icc 0 q) t) (t : ℝ) :
    HasDerivAt (periodicX X q hq) (periodicY Y q hq t) t := by
  exact hasDerivAt_periodicExtension (2 * q) (by linarith)
    (reflectedX X q) (reflectedY Y q)
    (hasDerivWithinAt_reflectedX hq hYq hX)
    (reflectedX_endpoints hq) (reflectedY_endpoints hq hY0) t

/-- The acceleration equation holds at every real time, including all joins. -/
theorem hasDerivAt_periodicY {X Y A : ℝ → ℝ} {q : ℝ}
    (hq : 0 < q) (hY0 : Y 0 = 0) (hYq : Y q = 0)
    (hY : ∀ t ∈ Icc 0 q, HasDerivWithinAt Y (A (X t)) (Icc 0 q) t) (t : ℝ) :
    HasDerivAt (periodicY Y q hq) (A (periodicX X q hq t)) t := by
  exact hasDerivAt_periodicExtension (2 * q) (by linarith)
    (reflectedY Y q) (fun s => A (reflectedX X q s))
    (hasDerivWithinAt_reflectedY hq hYq hY)
    (reflectedY_endpoints hq hY0) (congrArg A (reflectedX_endpoints hq)) t

/-- Every state of the complete path is an upper-arc state or its
momentum reflection. This transfers domain and energy properties. -/
theorem phase_cases (X Y : ℝ → ℝ) (q : ℝ) (hq : 0 < q) (t : ℝ) :
    ∃ s ∈ Icc 0 q, periodicX X q hq t = X s ∧
      (periodicY Y q hq t = Y s ∨ periodicY Y q hq t = -Y s) := by
  let r := toIcoMod (by linarith : 0 < 2 * q) 0 t
  have hr : r ∈ Ico 0 (2 * q) := toIcoMod_mem_Ico' _ t
  by_cases hrq : r ≤ q
  · refine ⟨r, ⟨hr.1, hrq⟩, ?_, Or.inl ?_⟩
    · exact reflectedX_eq_on_left hrq
    · exact reflectedY_eq_on_left hrq
  · refine ⟨2 * q - r, ⟨by linarith [hr.2], by linarith⟩, ?_, Or.inr ?_⟩
    · exact reflectedX_eq_on_right (le_of_not_ge hrq)
    · change (if r ≤ q then Y r else -Y (2 * q - r)) = -Y (2 * q - r)
      rw [if_neg hrq]

/-- Strict increase on the upper arc excludes an earlier return even at
the level of position. -/
theorem periodicX_gt_initial {X : ℝ → ℝ} {q t : ℝ} (hq : 0 < q)
    (hX : StrictMonoOn X (Icc 0 q)) (ht : t ∈ Ioo 0 (2 * q)) :
    periodicX X q hq 0 < periodicX X q hq t := by
  have hm : toIcoMod (by linarith : 0 < 2 * q) 0 t = t := by
    apply (toIcoMod_eq_self _).2
    simpa only [zero_add] using ⟨ht.1.le, ht.2⟩
  rw [periodicX_zero]
  simpa only [periodicX, periodicExtension, hm] using reflectedX_gt_initial hq hX ht

theorem no_initial_return (X Y : ℝ → ℝ) (q : ℝ) (hq : 0 < q)
    (hX : StrictMonoOn X (Icc 0 q)) {t : ℝ} (ht : t ∈ Ioo 0 (2 * q)) :
    (periodicX X q hq t, periodicY Y q hq t) ≠
      (periodicX X q hq 0, periodicY Y q hq 0) := by
  intro heq
  exact (ne_of_gt (periodicX_gt_initial hq hX ht)) (congrArg Prod.fst heq)

/-- Every positive period is at least the constructed period `2q`. -/
theorem least_period (X Y : ℝ → ℝ) (q : ℝ) (hq : 0 < q)
    (hX : StrictMonoOn X (Icc 0 q)) {p : ℝ} (hp : 0 < p)
    (hperiod : Function.Periodic
      (fun t => (periodicX X q hq t, periodicY Y q hq t)) p) :
    2 * q ≤ p := by
  by_contra hn
  have hreturn := hperiod 0
  simp only [zero_add] at hreturn
  exact no_initial_return X Y q hq hX ⟨hp, lt_of_not_ge hn⟩ hreturn

end LeanVerification.PeriodicReflection
