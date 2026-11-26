import LeanVerification.CauchyZeroCount
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace LeanVerification.MeasureSigns

def separatorSign {n : ℕ} (i : Fin (n + 1)) (j : Fin n) : ℝ :=
  if j.val < i.val then 1 else -1

def blockOrientation {n : ℕ} (i : Fin (n + 1)) : ℝ := ∏ j : Fin n, separatorSign i j

theorem blockOrientation_square {n : ℕ} (i : Fin (n + 1)) :
    blockOrientation i * blockOrientation i = 1 := by
  rw [blockOrientation, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j _
  simp only [separatorSign]
  split_ifs <;> norm_num

theorem blockOrientation_eq {n : ℕ} (i : Fin (n + 1)) :
    blockOrientation i = (-1 : ℝ) ^ (n - i.val) := by
  induction n with
  | zero => simp [blockOrientation]
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [blockOrientation, separatorSign]
      · rw [blockOrientation, Fin.prod_univ_succ]
        simp only [separatorSign, Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ,
          if_pos, one_mul, Nat.succ_lt_succ_iff, Nat.add_sub_add_right]
        exact ih j

/-- Explicit ordered sign-block data. The separators may repeat; every atom
belongs to one block, and each block contains nonzero input on a set of
positive reference measure. The global orientation is arbitrary and nonzero. -/
structure BlockDecomposition (μ : Measure ℝ) (f : ℝ → ℝ) (n : ℕ) where
  blocks : Fin (n + 1) → Set ℝ
  measurable : ∀ i, MeasurableSet (blocks i)
  disjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j))
  nonzero : ∀ i, ¬(∀ᵐ t ∂μ, t ∈ blocks i → f t = 0)
  cover : ∀ᵐ t ∂μ, f t ≠ 0 → ∃ i, t ∈ blocks i
  separators : Fin n → ℝ
  separator_nonneg : ∀ j, 0 ≤ separators j
  lower : ∀ i j, j.val < i.val → ∀ t ∈ blocks i, separators j ≤ t
  upper : ∀ i j, i.val ≤ j.val → ∀ t ∈ blocks i, t ≤ separators j
  orientation : ℝ
  orientation_ne_zero : orientation ≠ 0
  signs : ∀ i, ∀ᵐ t ∂μ, t ∈ blocks i →
    0 ≤ blockOrientation i * (orientation * f t)

theorem factoredDensity_nonnegative {μ : Measure ℝ} {f : ℝ → ℝ} {n : ℕ}
    (d : BlockDecomposition μ f n) :
    ∀ᵐ t ∂μ, 0 ≤ Cauchy.factoredDensity (List.ofFn d.separators)
      (fun t => d.orientation * f t) t := by
  have hall : ∀ᵐ t ∂μ, ∀ i, t ∈ d.blocks i →
      0 ≤ blockOrientation i * (d.orientation * f t) :=
    eventually_all.mpr d.signs
  filter_upwards [d.cover, hall] with t hcover hsign
  simp only [Cauchy.factoredDensity_eq_product, List.map_ofFn,
    Function.comp_def, List.prod_ofFn]
  by_cases hft : f t = 0
  · simp [hft]
  obtain ⟨i, hi⟩ := hcover hft
  have hfac : ∀ j : Fin n, 0 ≤ separatorSign i j * (t - d.separators j) := by
    intro j
    unfold separatorSign
    split_ifs with hj
    · simpa only [one_mul] using sub_nonneg.mpr (d.lower i j hj t hi)
    · have hh := d.upper i j (le_of_not_gt hj) t hi
      simp only [neg_one_mul]
      linarith
  have hprod : 0 ≤ ∏ j : Fin n, separatorSign i j * (t - d.separators j) :=
    Finset.prod_nonneg fun j _ => hfac j
  have hp := mul_nonneg hprod (hsign i hi)
  rw [Finset.prod_mul_distrib] at hp
  change 0 ≤ (blockOrientation i * ∏ j : Fin n, (t - d.separators j)) *
    (blockOrientation i * (d.orientation * f t)) at hp
  have he : (blockOrientation i * ∏ j : Fin n, (t - d.separators j)) *
      (blockOrientation i * (d.orientation * f t)) =
      (∏ j : Fin n, (t - d.separators j)) * (d.orientation * f t) := by
    calc
      _ = (blockOrientation i * blockOrientation i) *
          ((∏ j : Fin n, (t - d.separators j)) * (d.orientation * f t)) := by ring
      _ = _ := by rw [blockOrientation_square, one_mul]
  rwa [he] at hp

/-- The separator polynomial cannot annihilate all nonzero block mass:
that would inject `n+1` disjoint nonzero blocks into `n` separator indices. -/
theorem factoredDensity_nonzero {μ : Measure ℝ} {f : ℝ → ℝ} {n : ℕ}
    (d : BlockDecomposition μ f n) :
    ¬Cauchy.factoredDensity (List.ofFn d.separators)
      (fun t => d.orientation * f t) =ᵐ[μ] 0 := by
  classical
  intro hz
  have hpz : ∀ᵐ t ∂μ, (∏ j : Fin n, (t - d.separators j)) *
      (d.orientation * f t) = 0 := by
    filter_upwards [hz] with t ht
    simpa only [Cauchy.factoredDensity_eq_product, List.map_ofFn,
      Function.comp_def, List.prod_ofFn, Pi.zero_apply] using ht
  have hex : ∀ i : Fin (n + 1), ∃ j : Fin n,
      d.separators j ∈ d.blocks i ∧ f (d.separators j) ≠ 0 := by
    intro i
    by_contra hn
    apply d.nonzero i
    filter_upwards [hpz] with t ht
    intro hti
    by_cases hft : f t = 0
    · exact hft
    have hp : (∏ j : Fin n, (t - d.separators j)) = 0 :=
      (mul_eq_zero.mp ht).resolve_right (mul_ne_zero d.orientation_ne_zero hft)
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
    have htj : t = d.separators j := sub_eq_zero.mp hj
    exact (hn ⟨j, by simpa only [← htj] using hti, by simpa only [← htj] using hft⟩).elim
  choose k hk hknz using hex
  have hinj : Function.Injective k := by
    intro i j hij
    by_contra hne
    exact Set.disjoint_left.mp (d.disjoint hne) (hk i) (by simpa only [hij] using hk j)
  have hc := Fintype.card_le_of_injective k hinj
  simp only [Fintype.card_fin] at hc
  omega

/-- General Cauchy distinct-zero bound for ordered sign blocks, including
transition atoms and repeated separators. -/
theorem cauchy_atMostZeros {μ : Measure ℝ} {f : ℝ → ℝ} {β : ℝ} {n : ℕ}
    (d : BlockDecomposition μ f n) (hβ : 0 < β) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    FiniteZeroCounting.AtMostZeros n (Cauchy.transform μ f β) (Ioi 0) := by
  have hi : Integrable (fun t => (d.orientation * f t) * (1 + t) ^ (-β)) μ := by
    simpa only [mul_assoc] using hint.const_mul d.orientation
  have hc : ∀ c ∈ List.ofFn d.separators, 0 ≤ c := by
    intro c hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    exact d.separator_nonneg j
  have hb := Cauchy.atMostZeros_of_factor_certificate (List.ofFn d.separators) hc hβ
    (hf.const_mul d.orientation) hsupp hi (factoredDensity_nonnegative d)
      (factoredDensity_nonzero d)
  have he : Cauchy.transform μ (fun t => d.orientation * f t) β =
      fun δ => d.orientation * Cauchy.transform μ f β δ := by
    funext δ
    simp only [Cauchy.transform, mul_assoc, integral_const_mul]
  rw [List.length_ofFn, he] at hb
  exact (FiniteZeroCounting.atMostZeros_mul_iff (fun _ _ => d.orientation_ne_zero)).mp hb

theorem cauchy_nonvanishing {μ : Measure ℝ} {f : ℝ → ℝ} {β : ℝ} {n : ℕ}
    (d : BlockDecomposition μ f n) (hβ : 0 < β) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    ∃ δ > 0, Cauchy.transform μ f β δ ≠ 0 :=
  FiniteZeroCounting.exists_nonzero_Ioi (cauchy_atMostZeros d hβ hf hsupp hint)

/-- Ordinary ordered alternating blocks supply the separator data. Each
separator is the supremum of its preceding block; no strict gap is required. -/
theorem blockDecomposition_of_ordered_blocks {μ : Measure ℝ} {f : ℝ → ℝ} {n : ℕ}
    (B : Fin (n + 1) → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (hpos : ∀ i, B i ⊆ Ici 0)
    (horder : ∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y)
    (hnz : ∀ i, ¬(∀ᵐ t ∂μ, t ∈ B i → f t = 0))
    (hcover : ∀ᵐ t ∂μ, f t ≠ 0 → ∃ i, t ∈ B i)
    (q : ℝ) (hq : q ≠ 0)
    (hsign : ∀ i, ∀ᵐ t ∂μ, t ∈ B i → 0 ≤ (-1 : ℝ) ^ i.val * (q * f t)) :
    Nonempty (BlockDecomposition μ f n) := by
  classical
  have hne : ∀ i, (B i).Nonempty := by
    intro i
    by_contra hempty
    apply hnz i
    exact Eventually.of_forall fun t ht => (hempty ⟨t, ht⟩).elim
  have hbd : ∀ j : Fin n, BddAbove (B j.castSucc) := by
    intro j
    obtain ⟨u, hu⟩ := hne j.succ
    exact ⟨u, fun x hx => (horder _ _ (Fin.castSucc_lt_succ j) x hx u hu).le⟩
  let c : Fin n → ℝ := fun j => sSup (B j.castSucc)
  have hc : ∀ j, 0 ≤ c j := by
    intro j
    obtain ⟨u, hu⟩ := hne j.castSucc
    exact (hpos j.castSucc hu).trans (le_csSup (hbd j) hu)
  have hl : ∀ i j, j.val < i.val → ∀ t ∈ B i, c j ≤ t := by
    intro i j hij t ht
    exact csSup_le (hne j.castSucc) fun u hu =>
      (horder j.castSucc i hij u hu t ht).le
  have hu : ∀ i j, i.val ≤ j.val → ∀ t ∈ B i, t ≤ c j := by
    intro i j hij t ht
    by_cases he : i = j.castSucc
    · subst i
      exact le_csSup (hbd j) ht
    · have hij' : i < j.castSucc := by
        apply lt_of_le_of_ne hij
        exact fun hv => he (Fin.ext hv)
      obtain ⟨u, huu⟩ := hne j.castSucc
      exact (horder i j.castSucc hij' t ht u huu).le.trans (le_csSup (hbd j) huu)
  refine ⟨⟨B, hB, ?_, hnz, hcover, c, hc, hl, hu,
    (-1 : ℝ) ^ n * q, mul_ne_zero (pow_ne_zero n (by norm_num)) hq, ?_⟩⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (lt_irrefl t) (horder i j hlt t hti t htj)
    · exact (lt_irrefl t) (horder j i hgt t htj t hti)
  · intro i
    filter_upwards [hsign i] with t ht
    intro hti
    have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    have hp : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n - i.val) * (-1 : ℝ) ^ i.val := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    have hs : (-1 : ℝ) ^ (n - i.val) * (-1 : ℝ) ^ (n - i.val) = 1 := by
      rw [← mul_pow]
      norm_num
    have he : blockOrientation i * (((-1 : ℝ) ^ n * q) * f t) =
        (-1 : ℝ) ^ i.val * (q * f t) := by
      rw [blockOrientation_eq, hp]
      calc
        _ = ((-1 : ℝ) ^ (n - i.val) * (-1 : ℝ) ^ (n - i.val)) *
            ((-1 : ℝ) ^ i.val * (q * f t)) := by ring
        _ = _ := by rw [hs, one_mul]
    rw [he]
    exact ht hti

theorem cauchy_atMostZeros_of_ordered_blocks
    {μ : Measure ℝ} {f : ℝ → ℝ} {β : ℝ} {n : ℕ}
    (B : Fin (n + 1) → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (hpos : ∀ i, B i ⊆ Ici 0)
    (horder : ∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y)
    (hnz : ∀ i, ¬(∀ᵐ t ∂μ, t ∈ B i → f t = 0))
    (hcover : ∀ᵐ t ∂μ, f t ≠ 0 → ∃ i, t ∈ B i)
    (q : ℝ) (hq : q ≠ 0)
    (hsign : ∀ i, ∀ᵐ t ∂μ, t ∈ B i → 0 ≤ (-1 : ℝ) ^ i.val * (q * f t))
    (hβ : 0 < β) (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    FiniteZeroCounting.AtMostZeros n (Cauchy.transform μ f β) (Ioi 0) := by
  obtain ⟨d⟩ := blockDecomposition_of_ordered_blocks B hB hpos horder hnz hcover q hq hsign
  exact cauchy_atMostZeros d hβ hf hsupp hint

end LeanVerification.MeasureSigns
