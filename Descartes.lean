import LeanVerification.ScalarSeries
import LeanVerification.CountedZeros
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace LeanVerification.SequenceSigns

theorem pair_nonnegative_of_no_changes {a : ℕ → ℝ}
    (h : FiniteZeroCounting.AtMostSequenceSignChanges 0 a) (i j : ℕ) :
    0 ≤ a i * a j := by
  by_contra hn
  have hh : a i * a j < 0 := lt_of_not_ge hn
  have hi : a i ≠ 0 := (mul_ne_zero_iff.mp hh.ne).1
  have hj : a j ≠ 0 := (mul_ne_zero_iff.mp hh.ne).2
  rcases lt_trichotomy i j with hij | he | hji
  · exact no_chain h ((SignChain.single j hj).cons i hij hh)
  · rw [he] at hh
    exact (not_lt_of_ge (mul_self_nonneg _)) hh
  · exact no_chain h ((SignChain.single i hi).cons j hji (by rwa [mul_comm]))

end LeanVerification.SequenceSigns

namespace LeanVerification.ScalarSeries

open AnalyticMultiplicity SequenceSigns FiniteZeroCounting

theorem analyticOnNhd_positive {a : ℕ → ℝ} {R : ℝ}
    (hR : 0 < R) (h : ConvergesOn a R) : AnalyticOnNhd ℝ (sum a) (Ioo 0 R) := by
  apply (analyticOnNhd hR h).mono
  intro x hx
  exact ⟨by linarith [hx.1], hx.2⟩

theorem deriv_div_pow {a : ℕ → ℝ} {R x : ℝ}
    (hR : 0 < R) (h : ConvergesOn a R) (hx : x ∈ Ioo 0 R) (N : ℕ) :
    deriv (fun y => sum a y / y ^ N) x =
      sum (factorCoefficient N a) x / x ^ (N + 1) := by
  have ha := (analyticOnNhd_positive hR h x hx).differentiableAt.hasDerivAt
  have hd := ha.div ((hasDerivAt_id x).pow N) (pow_ne_zero N hx.1.ne')
  simp only [id_eq, one_mul] at hd
  rw [hd.deriv, sum_factor hR h (by simpa only [abs_of_pos hx.1] using hx.2)]
  cases N with
  | zero => simp [hx.1.ne']
  | succ n =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp [hx.1.ne']
      <;> ring

/-- The Euler coefficient reduction transfers a multiplicity bound back
to the original convergent series, with one extra zero allowed. -/
theorem multiplicityBound_of_factor {a : ℕ → ℝ} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (h : ConvergesOn a R) (N : ℕ)
    (hb : MultiplicityBound n (sum (factorCoefficient N a)) (Ioo 0 R)) :
    MultiplicityBound (n + 1) (sum a) (Ioo 0 R) := by
  let f : ℝ → ℝ := fun x => sum a x / x ^ N
  let g : ℝ → ℝ := sum (factorCoefficient N a)
  have ha := analyticOnNhd_positive hR h
  have hg : AnalyticOnNhd ℝ g (Ioo 0 R) :=
    analyticOnNhd_positive hR (h.factor hR N)
  have hf : AnalyticOnNhd ℝ f (Ioo 0 R) := by
    intro x hx
    exact (ha x hx).div (analyticAt_id.pow N) (pow_ne_zero N hx.1.ne')
  have hm (k : ℕ) : AnalyticOnNhd ℝ (fun x : ℝ => (x ^ k)⁻¹) (Ioo 0 R) := by
    intro x hx
    exact (analyticAt_id.pow k).inv (pow_ne_zero k hx.1.ne')
  have hmn (k : ℕ) : ∀ x ∈ Ioo (0 : ℝ) R, (x ^ k)⁻¹ ≠ 0 :=
    fun x hx => inv_ne_zero (pow_ne_zero k hx.1.ne')
  have hbmul : MultiplicityBound n (fun x => (x ^ (N + 1))⁻¹ * g x) (Ioo 0 R) :=
    (multiplicityBound_mul_nonvanishing_iff hg (hm _) (hmn _)).mpr hb
  have hbd : MultiplicityBound n (deriv f) (Ioo 0 R) := by
    apply hbmul.congrOn isOpen_Ioo (fun x hx => (hm _ x hx).mul (hg x hx))
      (fun x hx => (hf x hx).deriv)
    intro x hx
    rw [show deriv f x = g x / x ^ (N + 1) from deriv_div_pow hR h hx N]
    ring
  have hbf := multiplicityBound_of_derivative (convex_Ioo (0 : ℝ) R) hf hbd
  have he : f = fun x => (x ^ N)⁻¹ * sum a x := by
    funext x
    dsimp [f]
    ring
  rw [he] at hbf
  exact (multiplicityBound_mul_nonvanishing_iff ha (hm _) (hmn _)).mp hbf

theorem multiplicityBound_zero_of_one_sign {a : ℕ → ℝ} {R q : ℝ} {l : ℕ}
    (h : ConvergesOn a R) (hq : q ≠ 0)
    (hs : ∀ k, 0 ≤ q * a k) (hl : 0 < q * a l) :
    MultiplicityBound 0 (sum a) (Ioo 0 R) := by
  apply MultiplicityBound.of_nonvanishing
  intro x hx hzero
  have hp := sum_pos (h.const_mul q) hx hs hl
  rw [sum_const_mul, hzero, mul_zero] at hp
  exact lt_irrefl 0 hp

/-- Descartes' rule for an infinite convergent real power series.
The coefficient hypothesis uses increasing nonzero samples, so all zero
coefficients are omitted. The conclusion sums actual analytic orders. -/
theorem multiplicityBound_of_coefficient_sign_changes
    {a : ℕ → ℝ} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (h : ConvergesOn a R) (hne : ∃ k, a k ≠ 0)
    (hv : AtMostSequenceSignChanges n a) :
    MultiplicityBound n (sum a) (Ioo 0 R) := by
  classical
  induction n generalizing a with
  | zero =>
      obtain ⟨l, hl⟩ := hne
      exact multiplicityBound_zero_of_one_sign h hl
        (fun k => pair_nonnegative_of_no_changes hv l k) (mul_self_pos.mpr hl)
  | succ n ih =>
      let l := Nat.find hne
      have hl : a l ≠ 0 := Nat.find_spec hne
      have hprior : ∀ k < l, a k = 0 := by
        intro k hk
        exact not_ne_iff.mp (Nat.find_min hne hk)
      let q := a l
      let b : ℕ → ℝ := fun k => q * a k
      have hq : q ≠ 0 := hl
      have hbl : 0 < b l := mul_self_pos.mpr hl
      have hb : ConvergesOn b R := h.const_mul q
      by_cases hall : ∀ k, 0 ≤ b k
      · exact (multiplicityBound_zero_of_one_sign h hq hall hbl).mono_bound (Nat.zero_le _)
      · have hex : ∃ N, b N < 0 := by
          push_neg at hall
          exact hall
        let N := Nat.find hex
        have hN : b N < 0 := Nat.find_spec hex
        have hbefore : ∀ k < N, 0 ≤ b k := by
          intro k hk
          exact le_of_not_gt (Nat.find_min hex hk)
        have hlN : l < N := by
          by_contra hn
          have hle : N ≤ l := le_of_not_gt hn
          rcases hle.eq_or_lt with he | hlt
          · rw [he] at hN
            exact (not_lt_of_gt hbl) hN
          · have hz : b N = 0 := by simp only [b, hprior N hlt, mul_zero]
            rw [hz] at hN
            exact lt_irrefl 0 hN
        have hbc : AtMostSequenceSignChanges (n + 1) b := atMost_mul_const hv hq
        have hc : AtMostSequenceSignChanges n (factorCoefficient N b) :=
          atMost_factor_first_transition hbc hbefore hN hlN hbl
        have hcn : ∃ k, factorCoefficient N b k ≠ 0 := by
          refine ⟨l, mul_ne_zero ?_ hbl.ne'⟩
          apply sub_ne_zero.mpr
          exact_mod_cast hlN.ne
        have hcb := ih (hb.factor hR N) hcn hc
        have hbb := multiplicityBound_of_factor hR hb N hcb
        have he : sum b = fun x => q * sum a x := by
          funext x
          exact sum_const_mul a q x
        rw [he] at hbb
        exact (multiplicityBound_mul_nonvanishing_iff (analyticOnNhd_positive hR h)
          (fun _ _ => analyticAt_const) (fun _ _ => hq)).mp hbb

end LeanVerification.ScalarSeries
