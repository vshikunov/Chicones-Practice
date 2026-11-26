import LeanVerification.ZeroOrientation
import Mathlib.Order.Filter.Finite

/-!
# Strict sign changes under parameter limits

A strict sign-change bound is encoded by the absence of finitely many
ordered nonzero samples with alternating signs. Such a bound survives
pointwise convergence. This is the boundary-transfer step for signs in
the manuscript; it does not assert preservation of zero multiplicities.
-/

noncomputable section

namespace LeanVerification.SignVariation

open Set Filter
open scoped Topology

/-- `n` strict sign changes witnessed by `n+1` ordered nonzero samples. -/
def HasStrictSignChanges (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) : Prop :=
  ∃ x : Fin (n + 1) → ℝ, StrictMono x ∧ (∀ i, x i ∈ s) ∧
    (∀ i, f (x i) ≠ 0) ∧
    ∀ i : Fin n, f (x i.castSucc) * f (x i.succ) < 0

def AtMostStrictSignChanges (n : ℕ) (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ¬ HasStrictSignChanges f s (n + 1)

/-- Every finite alternating sample of the limit persists nearby. -/
theorem alternating_samples_persist {α : Type*} {l : Filter α}
    {F : α → ℝ → ℝ} {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hlim : ∀ x ∈ s, Tendsto (fun a => F a x) l (𝓝 (f x)))
    (hw : HasStrictSignChanges f s n) :
    ∀ᶠ a in l, HasStrictSignChanges (F a) s n := by
  obtain ⟨x, hmono, hmem, hnz, halt⟩ := hw
  have hevent_nz : ∀ i, ∀ᶠ a in l, F a (x i) ≠ 0 := by
    intro i
    exact (hlim (x i) (hmem i)).eventually (eventually_ne_nhds (hnz i))
  have hevent_alt : ∀ i : Fin n, ∀ᶠ a in l,
      F a (x i.castSucc) * F a (x i.succ) < 0 := by
    intro i
    have hp := (hlim (x i.castSucc) (hmem i.castSucc)).mul
      (hlim (x i.succ) (hmem i.succ))
    exact hp.eventually (isOpen_Iio.mem_nhds (halt i))
  filter_upwards [eventually_all.2 hevent_nz, eventually_all.2 hevent_alt] with a ha hb
  exact ⟨x, hmono, hmem, ha, hb⟩

/-- Strict sign-change bounds pass to pointwise limits, even if the limit
vanishes identically. No convergence of real-zero multiplicities is used. -/
theorem atMostStrictSignChanges_of_tendsto {α : Type*} {l : Filter α} [NeBot l]
    {F : α → ℝ → ℝ} {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hlim : ∀ x ∈ s, Tendsto (fun a => F a x) l (𝓝 (f x)))
    (hbound : ∀ᶠ a in l, AtMostStrictSignChanges n (F a) s) :
    AtMostStrictSignChanges n f s := by
  intro hw
  obtain ⟨a, ha, hb⟩ := (hbound.and (alternating_samples_persist hlim hw)).exists
  exact ha hb

theorem atMostStrictSignChanges_of_sequence {F : ℕ → ℝ → ℝ}
    {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hlim : ∀ x ∈ s, Tendsto (fun k => F k x) atTop (𝓝 (f x)))
    (hbound : ∀ k, AtMostStrictSignChanges n (F k) s) :
    AtMostStrictSignChanges n f s :=
  atMostStrictSignChanges_of_tendsto hlim (Eventually.of_forall hbound)

/-- Increasing comparison coordinates transport alternating samples to
the actual image of that coordinate. -/
theorem hasStrictSignChanges_comp {f χ : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hχ : StrictMonoOn χ s) (hw : HasStrictSignChanges (f ∘ χ) s n) :
    HasStrictSignChanges f (χ '' s) n := by
  obtain ⟨x, hx, hm, hn, ha⟩ := hw
  refine ⟨fun i => χ (x i), ?_, ?_, hn, ha⟩
  · intro i j hij
    exact hχ (hm i) (hm j) (hx hij)
  · intro i
    exact ⟨x i, hm i, rfl⟩

theorem atMostStrictSignChanges_comp {f χ : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hχ : StrictMonoOn χ s) (hb : AtMostStrictSignChanges n f (χ '' s)) :
    AtMostStrictSignChanges n (f ∘ χ) s :=
  fun hw => hb (hasStrictSignChanges_comp hχ hw)

/-- Samples in the actual image lift back to increasing coordinate samples. -/
theorem hasStrictSignChanges_of_image {f χ : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hχ : StrictMonoOn χ s) (hw : HasStrictSignChanges f (χ '' s) n) :
    HasStrictSignChanges (f ∘ χ) s n := by
  obtain ⟨x, hx, hm, hn, ha⟩ := hw
  let y : Fin (n + 1) → ℝ := fun i => Classical.choose (hm i)
  have hy : ∀ i, y i ∈ s ∧ χ (y i) = x i := fun i => Classical.choose_spec (hm i)
  refine ⟨y, ?_, fun i => (hy i).1, ?_, ?_⟩
  · intro i j hij
    by_contra hnot
    have hle := hχ.monotoneOn (hy j).1 (hy i).1 (le_of_not_gt hnot)
    rw [(hy j).2, (hy i).2] at hle
    exact (not_le_of_gt (hx hij)) hle
  · intro i
    simpa only [Function.comp_apply, (hy i).2] using hn i
  · intro i
    simpa only [Function.comp_apply, (hy i.castSucc).2, (hy i.succ).2] using ha i

theorem atMostStrictSignChanges_comp_iff {f χ : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hχ : StrictMonoOn χ s) :
    AtMostStrictSignChanges n (f ∘ χ) s ↔ AtMostStrictSignChanges n f (χ '' s) := by
  constructor
  · intro hb hw
    exact hb (hasStrictSignChanges_of_image hχ hw)
  · exact atMostStrictSignChanges_comp hχ

/-- The complete common-coordinate boundary transfer: the inputs may use
different increasing energy coordinates, but the limit bound returns to
the actual image of the limiting coordinate. -/
theorem atMostStrictSignChanges_of_coordinate_limit
    {α : Type*} {l : Filter α} [NeBot l]
    {F χ : α → ℝ → ℝ} {f ψ : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hχ : ∀ a, StrictMonoOn (χ a) s) (hψ : StrictMonoOn ψ s)
    (hlim : ∀ x ∈ s, Tendsto (fun a => F a (χ a x)) l (𝓝 (f (ψ x))))
    (hbound : ∀ᶠ a in l, AtMostStrictSignChanges n (F a) (χ a '' s)) :
    AtMostStrictSignChanges n f (ψ '' s) := by
  apply (atMostStrictSignChanges_comp_iff hψ).mp
  apply atMostStrictSignChanges_of_tendsto hlim
  exact hbound.mono fun a ha => atMostStrictSignChanges_comp (hχ a) ha

end LeanVerification.SignVariation
