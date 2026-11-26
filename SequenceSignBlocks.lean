import LeanVerification.FiniteZeroCounting
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section

open scoped BigOperators

namespace LeanVerification.SequenceSigns

open FiniteZeroCounting

/-- A finite witness of sign changes, with zero coefficients omitted. -/
structure SignChain (a : ℕ → ℝ) (n : ℕ) where
  index : Fin (n + 1) → ℕ
  increasing : StrictMono index
  nonzero : ∀ i, a (index i) ≠ 0
  opposite : ∀ i : Fin n, a (index i.castSucc) * a (index i.succ) < 0

theorem no_chain {a : ℕ → ℝ} {n : ℕ} (h : AtMostSequenceSignChanges n a)
    (c : SignChain a (n + 1)) : False :=
  h ⟨c.index, c.increasing, c.nonzero, c.opposite⟩

def SignChain.single {a : ℕ → ℝ} (k : ℕ) (hk : a k ≠ 0) : SignChain a 0 where
  index := fun _ => k
  increasing := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hh : i.val < j.val := hij
    omega
  nonzero := fun _ => hk
  opposite := Fin.elim0

def SignChain.cons {a : ℕ → ℝ} {n : ℕ} (c : SignChain a n)
    (k : ℕ) (hk : k < c.index 0) (hs : a k * a (c.index 0) < 0) :
    SignChain a (n + 1) where
  index := Fin.cons k c.index
  increasing := by
    apply Fin.strictMono_iff_lt_succ.mpr
    refine Fin.cases ?_ (fun i => ?_)
    · simpa using hk
    · simpa using c.increasing (Fin.castSucc_lt_succ i)
  nonzero := by
    refine Fin.cases ?_ (fun i => ?_)
    · simpa using (mul_ne_zero_iff.mp (ne_of_lt hs)).1
    · simpa using c.nonzero i
  opposite := by
    refine Fin.cases ?_ (fun i => ?_)
    · simpa using hs
    · simpa using c.opposite i

def SignChain.tail {a : ℕ → ℝ} {n : ℕ} (c : SignChain a (n + 1)) :
    SignChain a n where
  index := fun i => c.index i.succ
  increasing := c.increasing.comp Fin.strictMono_succ
  nonzero := fun i => c.nonzero i.succ
  opposite := fun i => c.opposite i.succ

def SignChain.unweight {a p : ℕ → ℝ} {n : ℕ}
    (c : SignChain (fun k => p k * a k) n)
    (hp : ∀ i, 0 < p (c.index i)) : SignChain a n where
  index := c.index
  increasing := c.increasing
  nonzero := fun i => (mul_ne_zero_iff.mp (c.nonzero i)).2
  opposite := by
    intro i
    have hh := c.opposite i
    have he : p (c.index i.castSucc) * a (c.index i.castSucc) *
        (p (c.index i.succ) * a (c.index i.succ)) =
        (p (c.index i.castSucc) * p (c.index i.succ)) *
          (a (c.index i.castSucc) * a (c.index i.succ)) := by ring
    rw [he] at hh
    exact neg_of_mul_neg_right hh (mul_pos (hp i.castSucc) (hp i.succ)).le

theorem atMost_mul_const {a : ℕ → ℝ} {n : ℕ} {q : ℝ}
    (h : AtMostSequenceSignChanges n a) (hq : q ≠ 0) :
    AtMostSequenceSignChanges n (fun k => q * a k) := by
  intro ⟨k, hk, hn, hs⟩
  apply h
  refine ⟨k, hk, fun i => (mul_ne_zero_iff.mp (hn i)).2, ?_⟩
  intro i
  have hh := hs i
  have hp : 0 < q * q := mul_self_pos.mpr hq
  have he : q * a (k i.castSucc) * (q * a (k i.succ)) =
      (q * q) * (a (k i.castSucc) * a (k i.succ)) := by ring
  rw [he] at hh
  exact neg_of_mul_neg_right hh hp.le

def factorCoefficient (c : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ := ((k : ℝ) - c) * a k

/-- Removing the first coefficient sign block reduces the number of
changes. The coefficient at the transition index is allowed to disappear. -/
theorem atMost_factor_first_transition {a : ℕ → ℝ} {n N l : ℕ}
    (h : AtMostSequenceSignChanges (n + 1) a)
    (hbefore : ∀ k < N, 0 ≤ a k) (hN : a N < 0)
    (hlN : l < N) (hl : 0 < a l) :
    AtMostSequenceSignChanges n (factorCoefficient N a) := by
  classical
  intro ⟨k, hk, hn, hs⟩
  let c : SignChain (factorCoefficient N a) (n + 1) := ⟨k, hk, hn, hs⟩
  have hneN : ∀ i, k i ≠ N := by
    intro i he
    apply hn i
    simp only [factorCoefficient, he, sub_self, zero_mul]
  by_cases hlow : k 0 < N
  · have han : 0 < a (k 0) := lt_of_le_of_ne (hbefore _ hlow)
      (fun he => (mul_ne_zero_iff.mp (hn 0)).2 he.symm)
    have hbn : factorCoefficient N a (k 0) < 0 := by
      have hcast : (k 0 : ℝ) < N := by exact_mod_cast hlow
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hcast) han
    have hb1 : 0 < factorCoefficient N a (k (Fin.succ 0)) := by
      have hh := hs (0 : Fin (n + 1))
      exact pos_of_mul_neg_right hh hbn.le
    have hhigh : N < k (Fin.succ 0) := by
      by_contra hh
      have hle : k (Fin.succ 0) ≤ N := le_of_not_gt hh
      have hlt : k (Fin.succ 0) < N := lt_of_le_of_ne hle (hneN _)
      have hc : (k (Fin.succ 0) : ℝ) ≤ N := by exact_mod_cast hle
      have hnonpos : factorCoefficient N a (k (Fin.succ 0)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hc) (hbefore _ hlt)
      exact (not_le_of_gt hb1) hnonpos
    have hp : ∀ i : Fin (n + 1), 0 < ((c.tail.index i : ℕ) : ℝ) - N := by
      intro i
      have hi : N < k i.succ := hhigh.trans_le (hk.monotone (Fin.succ_le_succ_iff.mpr (Fin.zero_le _)))
      exact sub_pos.mpr (by exact_mod_cast hi)
    let d : SignChain a n := c.tail.unweight hp
    have hd0 : 0 < a (d.index 0) := by
      exact (mul_pos_iff_of_pos_left (hp 0)).mp hb1
    let e : SignChain a (n + 1) := d.cons N hhigh (mul_neg_of_neg_of_pos hN hd0)
    exact no_chain h (e.cons (k 0) hlow (mul_neg_of_pos_of_neg han hN))
  · have hhigh : N < k 0 := lt_of_le_of_ne (le_of_not_gt hlow) (hneN 0).symm
    have hp : ∀ i, 0 < ((c.index i : ℕ) : ℝ) - N := by
      intro i
      have hi : N < k i := hhigh.trans_le (hk.monotone (Fin.zero_le _))
      exact sub_pos.mpr (by exact_mod_cast hi)
    let d : SignChain a (n + 1) := c.unweight hp
    rcases lt_or_gt_of_ne (d.nonzero 0) with hneg | hpos
    · exact no_chain h (d.cons l (hlN.trans hhigh) (mul_neg_of_pos_of_neg hl hneg))
    · exact no_chain h (d.cons N hhigh (mul_neg_of_neg_of_pos hN hpos))

end LeanVerification.SequenceSigns
