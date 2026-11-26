import LeanVerification.AnalyticMultiplicity
import Mathlib.Data.Finset.Sort

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace LeanVerification.AnalyticMultiplicity

theorem MultiplicityBound.mono_bound {f : ℝ → ℝ} {s : Set ℝ} {n m : ℕ}
    (h : MultiplicityBound n f s) (hnm : n ≤ m) : MultiplicityBound m f s := by
  intro z hz
  exact (h z hz).trans (by exact_mod_cast hnm)

theorem MultiplicityBound.of_nonvanishing {f : ℝ → ℝ} {s : Set ℝ}
    (h : ∀ x ∈ s, f x ≠ 0) : MultiplicityBound 0 f s := by
  classical
  intro z hz
  have he : z = ∅ := Finset.eq_empty_iff_forall_not_mem.mpr (by
    intro x hx
    exact h x (hz x hx).1 (hz x hx).2)
  simp only [he, Finset.sum_empty, Nat.cast_zero, le_refl]

theorem vanishingOrder_congr {f g : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) (he : f =ᶠ[𝓝 x] g) :
    vanishingOrder f x = vanishingOrder g x := by
  rw [vanishingOrder_eq hf, vanishingOrder_eq hg]
  exact (hf.order_congr he).symm

theorem MultiplicityBound.congrOn {f g : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (h : MultiplicityBound n f s) (hs : IsOpen s)
    (hf : AnalyticOnNhd ℝ f s) (hg : AnalyticOnNhd ℝ g s)
    (he : ∀ x ∈ s, f x = g x) : MultiplicityBound n g s := by
  apply multiplicityBound_of_zero_order_transport h
  intro x hx hzero
  refine ⟨hx, (he x hx).trans hzero, ?_⟩
  apply vanishingOrder_congr (hg x hx) (hf x hx)
  filter_upwards [hs.mem_nhds hx] with y hy
  exact (he y hy).symm

theorem vanishingOrder_eq_zero_of_ne_zero {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hx : f x ≠ 0) : vanishingOrder f x = 0 := by
  rw [vanishingOrder_eq hf]
  exact hf.order_eq_zero_iff.mpr hx

theorem one_le_vanishingOrder_of_zero {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hx : f x = 0) : 1 ≤ vanishingOrder f x := by
  rw [vanishingOrder_eq hf]
  apply ENat.one_le_iff_ne_zero.mpr
  intro ho
  exact hf.order_eq_zero_iff.mp ho hx

/-- Differentiation lowers a positive analytic order by exactly one,
including the infinite order of a locally zero germ. -/
theorem vanishingOrder_eq_deriv_add_one {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hx : f x = 0) :
    vanishingOrder f x = vanishingOrder (deriv f) x + 1 := by
  rw [vanishingOrder_eq hf, vanishingOrder_eq hf.deriv]
  by_cases ht : hf.order = ⊤
  · have he : f =ᶠ[𝓝 x] fun _ => 0 := hf.order_eq_top_iff.mp ht
    have hd : hf.deriv.order = ⊤ := hf.deriv.order_eq_top_iff.mpr (by
      filter_upwards [he.deriv] with t hdt
      simpa only [deriv_const] using hdt)
    simp only [ht, hd, top_add]
  · have hn : hf.order = (hf.order.toNat : ENat) := (ENat.coe_toNat ht).symm
    have hp : hf.order.toNat ≠ 0 := by
      intro hz
      rw [hz] at hn
      exact hf.order_eq_zero_iff.mp hn hx
    obtain ⟨n, hsucc⟩ := Nat.exists_eq_succ_of_ne_zero hp
    rw [hsucc] at hn
    have hd := order_deriv_of_order_succ hf hn
    rw [hn, hd]
    norm_cast

/-- Nonzeros have order zero, so a multiplicity bound also bounds the
order sum on an arbitrary finite subset of the analytic domain. -/
theorem MultiplicityBound.sum_le {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hb : MultiplicityBound n f s) (hf : AnalyticOnNhd ℝ f s)
    (z : Finset ℝ) (hz : ∀ x ∈ z, x ∈ s) :
    ∑ x ∈ z, vanishingOrder f x ≤ (n : ENat) := by
  classical
  have he : ∑ x ∈ z.filter (fun x => f x = 0), vanishingOrder f x =
      ∑ x ∈ z, vanishingOrder f x := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hn
    apply vanishingOrder_eq_zero_of_ne_zero (hf x (hz x hx))
    intro hfx
    exact hn (Finset.mem_filter.mpr ⟨hx, hfx⟩)
  rw [← he]
  apply hb
  intro x hx
  obtain ⟨hxz, hfx⟩ := Finset.mem_filter.mp hx
  exact ⟨hz x hxz, hfx⟩

/-- Adjacent roots give a disjoint finite set of intervening derivative
roots. The cardinality is one less than that of the original set. -/
theorem exists_disjoint_derivative_zeros {f : ℝ → ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (z : Finset ℝ) (hz : ∀ x ∈ z, x ∈ s ∧ f x = 0) (hne : z.Nonempty) :
    ∃ w : Finset ℝ, Disjoint z w ∧ w.card + 1 = z.card ∧
      ∀ x ∈ w, x ∈ s ∧ deriv f x = 0 := by
  classical
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hne)
  let x : Fin (k + 1) ↪o ℝ := z.orderEmbOfFin hk
  have hxz : ∀ i, x i ∈ z := fun i => z.orderEmbOfFin_mem hk i
  have he : ∀ i : Fin k, ∃ c : ℝ,
      c ∈ Ioo (x i.castSucc) (x i.succ) ∧ deriv f c = 0 := by
    intro i
    have hsub : Icc (x i.castSucc) (x i.succ) ⊆ s :=
      hs.ordConnected.out (hz _ (hxz _)).1 (hz _ (hxz _)).1
    exact exists_deriv_eq_zero (x.strictMono (Fin.castSucc_lt_succ i))
      (hf.mono hsub) ((hz _ (hxz _)).2.trans (hz _ (hxz _)).2.symm)
  choose c hc hdc using he
  have hmono : StrictMono c := by
    intro i j hij
    have hij' : i.succ ≤ j.castSucc := Nat.succ_le_of_lt hij
    exact (hc i).2.trans_le ((x.monotone hij').trans (hc j).1.le)
  refine ⟨Finset.univ.image c, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro t htz htw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp htw
    have hrg : c i ∈ Set.range x := by
      rw [show Set.range x = (z : Set ℝ) from z.range_orderEmbOfFin hk]
      exact htz
    obtain ⟨j, hj⟩ := hrg
    by_cases hji : j ≤ i.castSucc
    · have hle : x j ≤ x i.castSucc := x.monotone hji
      rw [hj] at hle
      exact (not_le_of_gt (hc i).1) hle
    · have hij : i.succ ≤ j := by
        change i.val + 1 ≤ j.val
        have hh : ¬j.val ≤ i.val := hji
        omega
      have hle : x i.succ ≤ x j := x.monotone hij
      rw [hj] at hle
      exact (not_le_of_gt (hc i).2) hle
  · rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ,
      Fintype.card_fin, hk]
  · intro t ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨hs.ordConnected.out (hz _ (hxz _)).1 (hz _ (hxz _)).1
      ⟨(hc i).1.le, (hc i).2.le⟩, hdc i⟩

/-- Rolle's theorem with sums of the actual analytic orders. This
includes repeated roots and locally zero analytic germs. -/
theorem multiplicityBound_of_derivative {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hs : Convex ℝ s) (hf : AnalyticOnNhd ℝ f s)
    (hd : MultiplicityBound n (deriv f) s) : MultiplicityBound (n + 1) f s := by
  classical
  intro z hz
  by_cases hne : z.Nonempty
  · obtain ⟨w, hdj, hcard, hw⟩ := exists_disjoint_derivative_zeros hs hf.continuousOn z hz hne
    have hwone : (w.card : ENat) ≤ ∑ x ∈ w, vanishingOrder (deriv f) x := by
      calc
        (w.card : ENat) = ∑ _x ∈ w, (1 : ENat) := by simp
        _ ≤ _ := Finset.sum_le_sum fun x hx =>
          one_le_vanishingOrder_of_zero (hf x (hw x hx).1).deriv (hw x hx).2
    have hbound := hd.sum_le (fun x hx => (hf x hx).deriv) (z ∪ w) (by
      intro x hx
      rcases Finset.mem_union.mp hx with hzx | hwx
      · exact (hz x hzx).1
      · exact (hw x hwx).1)
    rw [Finset.sum_union hdj] at hbound
    have hsum : ∑ x ∈ z, vanishingOrder f x =
        (∑ x ∈ z, vanishingOrder (deriv f) x) + (z.card : ENat) := by
      calc
        _ = ∑ x ∈ z, (vanishingOrder (deriv f) x + 1) :=
          Finset.sum_congr rfl fun x hx => vanishingOrder_eq_deriv_add_one
            (hf x (hz x hx).1) (hz x hx).2
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    rw [hsum, ← hcard]
    norm_cast at *
    calc
      (∑ x ∈ z, vanishingOrder (deriv f) x) + ((w.card + 1 : ℕ) : ENat) =
          ((∑ x ∈ z, vanishingOrder (deriv f) x) + (w.card : ENat)) + 1 := by
            rw [Nat.cast_add, Nat.cast_one, add_assoc]
      _ ≤ ((∑ x ∈ z, vanishingOrder (deriv f) x) +
          ∑ x ∈ w, vanishingOrder (deriv f) x) + 1 :=
            add_le_add_right (add_le_add_left hwone _) _
      _ ≤ (n : ENat) + 1 := add_le_add_right hbound _
      _ = ((n + 1 : ℕ) : ENat) := by norm_cast
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, zero_le]

theorem multiplicityBound_mul_nonvanishing_iff {f a : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hf : AnalyticOnNhd ℝ f s) (ha : AnalyticOnNhd ℝ a s)
    (hn : ∀ x ∈ s, a x ≠ 0) :
    MultiplicityBound n (fun x => a x * f x) s ↔ MultiplicityBound n f s := by
  have hm : AnalyticOnNhd ℝ (fun x => a x * f x) s := fun x hx => (ha x hx).mul (hf x hx)
  have he : ∀ x ∈ s, vanishingOrder (fun x => a x * f x) x = vanishingOrder f x := by
    intro x hx
    rw [vanishingOrder_eq (hm x hx), vanishingOrder_eq (hf x hx),
      (ha x hx).order_mul (hf x hx), (ha x hx).order_eq_zero_iff.mpr (hn x hx), zero_add]
  constructor
  · intro hb
    apply multiplicityBound_of_zero_order_transport hb
    intro x hx hfx
    exact ⟨hx, by simp only [hfx, mul_zero], (he x hx).symm⟩
  · intro hb
    apply multiplicityBound_of_zero_order_transport hb
    intro x hx hfx
    exact ⟨hx, (mul_eq_zero.mp hfx).resolve_left (hn x hx), he x hx⟩

end LeanVerification.AnalyticMultiplicity
