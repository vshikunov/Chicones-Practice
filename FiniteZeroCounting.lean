import LeanVerification.SignVariation
import Mathlib.Order.Fin.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

noncomputable section

open Set Filter
open scoped Topology

namespace LeanVerification.FiniteZeroCounting

/-- A strictly ordered family of `n` distinct zeros in a prescribed set. -/
def HasOrderedZeros (n : ℕ) (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ x : Fin n → ℝ, StrictMono x ∧ ∀ i, x i ∈ s ∧ f (x i) = 0

def AtMostZeros (n : ℕ) (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ¬HasOrderedZeros (n + 1) f s

theorem HasOrderedZeros.mono {n : ℕ} {f : ℝ → ℝ} {s t : Set ℝ}
    (hz : HasOrderedZeros n f s) (hst : s ⊆ t) : HasOrderedZeros n f t := by
  obtain ⟨x, hx, hz⟩ := hz
  exact ⟨x, hx, fun i => ⟨hst (hz i).1, (hz i).2⟩⟩

theorem AtMostZeros.mono {n : ℕ} {f : ℝ → ℝ} {s t : Set ℝ}
    (hz : AtMostZeros n f t) (hst : s ⊆ t) : AtMostZeros n f s :=
  fun h => hz (h.mono hst)

theorem atMostZeros_zero_iff {f : ℝ → ℝ} {s : Set ℝ} :
    AtMostZeros 0 f s ↔ ∀ x ∈ s, f x ≠ 0 := by
  constructor
  · intro h x hx hz
    apply h
    refine ⟨fun _ => x, ?_, fun _ => ⟨hx, hz⟩⟩
    intro i j hij
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    have hh : i.val < j.val := hij
    omega
  · intro h ⟨x, _, hx⟩
    exact h (x 0) (hx 0).1 (hx 0).2

/-- Rolle's theorem supplies one strictly ordered derivative zero in each
successive gap. Only continuity on the interval is needed for this step. -/
theorem orderedZeros_derivative {n : ℕ} {f : ℝ → ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hz : HasOrderedZeros (n + 1) f s) :
    HasOrderedZeros n (deriv f) s := by
  obtain ⟨x, hx, hz⟩ := hz
  have he : ∀ i : Fin n, ∃ c : ℝ,
      c ∈ Ioo (x i.castSucc) (x i.succ) ∧ deriv f c = 0 := by
    intro i
    have hxy := hx (Fin.castSucc_lt_succ i)
    have hsub : Icc (x i.castSucc) (x i.succ) ⊆ s :=
      hs.ordConnected.out (hz i.castSucc).1 (hz i.succ).1
    exact exists_deriv_eq_zero hxy (hf.mono hsub)
      ((hz i.castSucc).2.trans (hz i.succ).2.symm)
  choose c hc hdc using he
  refine ⟨c, ?_, ?_⟩
  · intro i j hij
    have hij' : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact Nat.succ_le_of_lt hij
    exact (hc i).2.trans_le ((hx.monotone hij').trans (hc j).1.le)
  · intro i
    exact ⟨hs.ordConnected.out (hz i.castSucc).1 (hz i.succ).1
      ⟨(hc i).1.le, (hc i).2.le⟩, hdc i⟩

theorem atMostZeros_of_derivative {n : ℕ} {f : ℝ → ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hd : AtMostZeros n (deriv f) s) : AtMostZeros (n + 1) f s :=
  fun hz => hd (orderedZeros_derivative hs hf hz)

/-- A root at the boundary is allowed, but every intervening Rolle root
lies strictly inside the half-line. No endpoint derivative is required. -/
theorem orderedZeros_derivative_Ici {n : ℕ} {f : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousOn f (Ici a)) (hz : HasOrderedZeros (n + 1) f (Ici a)) :
    HasOrderedZeros n (deriv f) (Ioi a) := by
  obtain ⟨x, hx, hz⟩ := hz
  have he : ∀ i : Fin n, ∃ c : ℝ,
      c ∈ Ioo (x i.castSucc) (x i.succ) ∧ deriv f c = 0 := by
    intro i
    have hsub : Icc (x i.castSucc) (x i.succ) ⊆ Ici a := by
      intro t ht
      exact (hz i.castSucc).1.trans ht.1
    exact exists_deriv_eq_zero (hx (Fin.castSucc_lt_succ i)) (hf.mono hsub)
      ((hz i.castSucc).2.trans (hz i.succ).2.symm)
  choose c hc hdc using he
  refine ⟨c, ?_, ?_⟩
  · intro i j hij
    have hij' : i.succ ≤ j.castSucc := Nat.succ_le_of_lt hij
    exact (hc i).2.trans_le ((hx.monotone hij').trans (hc j).1.le)
  · intro i
    exact ⟨(hz i.castSucc).1.trans_lt (hc i).1, hdc i⟩

theorem orderedZeros_of_same_zeros {n : ℕ} {f g : ℝ → ℝ} {s : Set ℝ}
    (he : ∀ x ∈ s, f x = 0 ↔ g x = 0) (hf : HasOrderedZeros n f s) :
    HasOrderedZeros n g s := by
  obtain ⟨x, hx, hz⟩ := hf
  exact ⟨x, hx, fun i => ⟨(hz i).1, (he (x i) (hz i).1).mp (hz i).2⟩⟩

theorem atMostZeros_of_same_zeros {n : ℕ} {f g : ℝ → ℝ} {s : Set ℝ}
    (he : ∀ x ∈ s, f x = 0 ↔ g x = 0) (hf : AtMostZeros n f s) :
    AtMostZeros n g s := by
  intro hz
  exact hf (orderedZeros_of_same_zeros (fun x hx => (he x hx).symm) hz)

theorem atMostZeros_mul_iff {n : ℕ} {f w : ℝ → ℝ} {s : Set ℝ}
    (hw : ∀ x ∈ s, w x ≠ 0) :
    AtMostZeros n (fun x => w x * f x) s ↔ AtMostZeros n f s := by
  have he : ∀ x ∈ s, w x * f x = 0 ↔ f x = 0 := by
    intro x hx
    simp only [mul_eq_zero, hw x hx, false_or]
  exact ⟨atMostZeros_of_same_zeros he,
    atMostZeros_of_same_zeros (fun x hx => (he x hx).symm)⟩

/-- A finite zero bound excludes an identically zero function on a half-line. -/
theorem exists_nonzero_Ioi {n : ℕ} {f : ℝ → ℝ} {a : ℝ}
    (hf : AtMostZeros n f (Ioi a)) : ∃ x ∈ Ioi a, f x ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hf
  refine ⟨fun i => a + (i : ℝ) + 1, ?_, ?_⟩
  · intro i j hij
    have hcast : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    exact add_lt_add_right (add_lt_add_left hcast a) 1
  · intro i
    have hi : a < a + (i : ℝ) + 1 := by
      have hn : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
      linarith
    exact ⟨hi, hn _ hi⟩

theorem orderedZeros_of_strictSignChanges {n : ℕ} {f : ℝ → ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hv : SignVariation.HasStrictSignChanges f s n) : HasOrderedZeros n f s := by
  obtain ⟨x, hx, hm, hn, ha⟩ := hv
  have he : ∀ i : Fin n, ∃ c : ℝ, c ∈ Ioo (x i.castSucc) (x i.succ) ∧ f c = 0 := by
    intro i
    have hxy := hx (Fin.castSucc_lt_succ i)
    have hc := hf.mono (hs.ordConnected.out (hm i.castSucc) (hm i.succ))
    rcases mul_neg_iff.mp (ha i) with hsign | hsign
    · exact intermediate_value_Ioo' hxy.le hc ⟨hsign.2, hsign.1⟩
    · exact intermediate_value_Ioo hxy.le hc ⟨hsign.1, hsign.2⟩
  choose c hc hfc using he
  refine ⟨c, ?_, ?_⟩
  · intro i j hij
    have hij' : i.succ ≤ j.castSucc := Nat.succ_le_of_lt hij
    exact (hc i).2.trans_le ((hx.monotone hij').trans (hc j).1.le)
  · intro i
    exact ⟨hs.ordConnected.out (hm i.castSucc) (hm i.succ)
      ⟨(hc i).1.le, (hc i).2.le⟩, hfc i⟩

theorem atMostStrictSignChanges_of_zero_bound {n : ℕ} {f : ℝ → ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s) (hz : AtMostZeros n f s) :
    SignVariation.AtMostStrictSignChanges n f s :=
  fun hv => hz (orderedZeros_of_strictSignChanges hs hf hv)

/-- Sign changes in a sequence are witnessed by increasing indices with
alternating nonzero entries; intervening zero entries are omitted. -/
def AtMostSequenceSignChanges (n : ℕ) (a : ℕ → ℝ) : Prop :=
  ¬∃ k : Fin (n + 2) → ℕ, StrictMono k ∧
    (∀ i, a (k i) ≠ 0) ∧ ∀ i : Fin (n + 1), a (k i.castSucc) * a (k i.succ) < 0

theorem sequence_signVariation_of_zero_bound {n : ℕ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ici 0)) (hz : AtMostZeros n f (Ici 0)) :
    AtMostSequenceSignChanges n (fun k => f (k : ℝ)) := by
  intro ⟨k, hk, hn, ha⟩
  apply atMostStrictSignChanges_of_zero_bound (convex_Ici (0 : ℝ)) hf hz
  refine ⟨fun i => (k i : ℝ), ?_, ?_, hn, ha⟩
  · intro i j hij
    change (k i : ℝ) < (k j : ℝ)
    exact_mod_cast hk hij
  · intro i
    change (0 : ℝ) ≤ (k i : ℝ)
    exact Nat.cast_nonneg _

end LeanVerification.FiniteZeroCounting
