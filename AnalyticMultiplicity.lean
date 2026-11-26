import LeanVerification.AnalyticReparametrization
import LeanVerification.ZeroOrientation
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
Vanishing orders and ordinary derivatives. These statements concern actual
analytic germs and their derivatives, rather than a separately supplied
integer labelled as a multiplicity.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace LeanVerification.AnalyticMultiplicity

theorem order_deriv_of_order_succ {f : ℝ → ℝ} {x : ℝ} {n : ℕ}
    (hf : AnalyticAt ℝ f x) (ho : hf.order = ((n + 1 : ℕ) : ENat)) :
    hf.deriv.order = (n : ENat) := by
  obtain ⟨g, hg, hgn, he⟩ := hf.order_eq_nat_iff.mp ho
  let q : ℝ → ℝ := fun t => (n + 1 : ℝ) * g t + (t - x) * deriv g t
  have hq : AnalyticAt ℝ q x :=
    (analyticAt_const.mul hg).add ((analyticAt_id.sub analyticAt_const).mul hg.deriv)
  have hqn : q x ≠ 0 := by
    simpa [q] using mul_ne_zero (by positivity : (n + 1 : ℝ) ≠ 0) hgn
  apply hf.deriv.order_eq_nat_iff.mpr
  refine ⟨q, hq, hqn, ?_⟩
  have he' : f =ᶠ[𝓝 x] fun z => (z - x) ^ (n + 1) • g z := he
  have hed := he'.deriv
  filter_upwards [hed, hg.eventually_analyticAt] with t ht hgt
  rw [ht]
  have hd := (((hasDerivAt_id t).sub_const x).pow (n + 1)).mul
    hgt.differentiableAt.hasDerivAt
  simp only [id_eq] at hd
  have hde : deriv (fun z => (z - x) ^ (n + 1) • g z) t =
      (t - x) ^ n * q t := by
    simp only [smul_eq_mul]
    rw [hd.deriv]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, sub_zero, one_mul,
      pow_succ, q]
    ring
  simpa only [smul_eq_mul] using hde

theorem order_ne_top_of_deriv_ne_zero {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hd : deriv f x ≠ 0) : hf.order ≠ ⊤ := by
  intro ho
  have he : f =ᶠ[𝓝 x] fun _ => 0 := hf.order_eq_top_iff.mp ho
  have hz := he.deriv_eq
  simp only [deriv_const] at hz
  exact hd hz

theorem order_eq_one_of_deriv_ne_zero {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hz : f x = 0) (hd : deriv f x ≠ 0) :
    hf.order = 1 := by
  have hn := order_ne_top_of_deriv_ne_zero hf hd
  have hnat : hf.order = (hf.order.toNat : ENat) := (ENat.coe_toNat hn).symm
  have hpos : hf.order.toNat ≠ 0 := by
    intro hzero
    rw [hzero] at hnat
    exact (hf.order_eq_zero_iff.mp hnat) hz
  obtain ⟨n, he⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  rw [he] at hnat
  have hdorder := order_deriv_of_order_succ hf hnat
  have hdn := hf.deriv.order_eq_zero_iff.mpr hd
  rw [hdn] at hdorder
  have hn0 : n = 0 := by exact_mod_cast hdorder.symm
  simpa [hn0] using hnat

theorem order_eq_two_of_second_deriv_ne_zero {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hz : f x = 0) (hdz : deriv f x = 0)
    (hdd : deriv (deriv f) x ≠ 0) : hf.order = 2 := by
  have hn : hf.order ≠ ⊤ := by
    intro ho
    have he : f =ᶠ[𝓝 x] fun _ => 0 := hf.order_eq_top_iff.mp ho
    have hz' := he.deriv.deriv_eq
    have hc : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
      funext t
      exact deriv_const t 0
    rw [hc, deriv_const] at hz'
    exact hdd hz'
  have hnat : hf.order = (hf.order.toNat : ENat) := (ENat.coe_toNat hn).symm
  have hpos : hf.order.toNat ≠ 0 := by
    intro hzero
    rw [hzero] at hnat
    exact (hf.order_eq_zero_iff.mp hnat) hz
  obtain ⟨n, he⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  rw [he] at hnat
  have hdorder := order_deriv_of_order_succ hf hnat
  have hdn := order_eq_one_of_deriv_ne_zero hf.deriv hdz hdd
  rw [hdn] at hdorder
  have hn1 : n = 1 := by exact_mod_cast hdorder.symm
  simpa [hn1] using hnat

open scoped Classical in
def vanishingOrder (f : ℝ → ℝ) (x : ℝ) : ENat :=
  if hf : AnalyticAt ℝ f x then hf.order else 0

theorem vanishingOrder_eq {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) :
    vanishingOrder f x = hf.order := by
  simp only [vanishingOrder, dif_pos hf]

/-- A bound on the sum of the actual analytic orders for every finite
collection of distinct zeros. Infinite-order germs are included. -/
def MultiplicityBound (n : ℕ) (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ z : Finset ℝ, (∀ x ∈ z, x ∈ s ∧ f x = 0) →
    ∑ x ∈ z, vanishingOrder f x ≤ (n : ENat)

theorem stationary_zero_is_only_zero {f : ℝ → ℝ} {a b x y : ℝ}
    (hf : ContinuousOn f (Ioo a b))
    (hc : ZeroCounting.AtMostOneZeroOn (deriv f) (Ioo a b))
    (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    (hzx : f x = 0) (hzy : f y = 0) (hdx : deriv f x = 0) : y = x := by
  rcases lt_trichotomy x y with hxy | he | hyx
  · have hs : Icc x y ⊆ Ioo a b := (convex_Ioo a b).ordConnected.out hx hy
    obtain ⟨c, hcm, hdc⟩ := exists_deriv_eq_zero hxy (hf.mono hs) (hzx.trans hzy.symm)
    have hcI : c ∈ Ioo a b := hs ⟨hcm.1.le, hcm.2.le⟩
    have hec := hc hx hcI hdx hdc
    exact False.elim ((ne_of_lt hcm.1) hec)
  · exact he.symm
  · have hs : Icc y x ⊆ Ioo a b := (convex_Ioo a b).ordConnected.out hy hx
    obtain ⟨c, hcm, hdc⟩ := exists_deriv_eq_zero hyx (hf.mono hs) (hzy.trans hzx.symm)
    have hcI : c ∈ Ioo a b := hs ⟨hcm.1.le, hcm.2.le⟩
    have hec := hc hcI hx hdc hdx
    exact False.elim ((ne_of_lt hcm.2) hec)

theorem multiplicityBound_two_of_stationary_curvature {f : ℝ → ℝ} {a b : ℝ}
    (hf : AnalyticOnNhd ℝ f (Ioo a b))
    (hcurv : ∀ x ∈ Ioo a b, deriv f x = 0 → 0 < deriv (deriv f) x) :
    MultiplicityBound 2 f (Ioo a b) := by
  classical
  have hdf : DifferentiableOn ℝ f (Ioo a b) := fun x hx =>
    (hf x hx).differentiableAt.differentiableWithinAt
  have hddf : DifferentiableOn ℝ (deriv f) (Ioo a b) := fun x hx =>
    (hf x hx).deriv.differentiableAt.differentiableWithinAt
  have hcrit := ZeroOrientation.atMostOneZeroOn_Ioo_of_deriv_pos_at_zeros hddf hcurv
  have htwo := ZeroCounting.atMostTwoZerosOn_of_deriv_atMostOne hdf hcrit
  intro z hz
  by_cases hstat : ∃ x ∈ z, deriv f x = 0
  · obtain ⟨x, hx, hdx⟩ := hstat
    have heq : z = {x} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hx, ?_⟩
      intro y hy
      exact stationary_zero_is_only_zero hf.continuousOn hcrit (hz x hx).1
        (hz y hy).1 (hz x hx).2 (hz y hy).2 hdx
    rw [heq, Finset.sum_singleton, vanishingOrder_eq (hf x (hz x hx).1)]
    exact le_of_eq (order_eq_two_of_second_deriv_ne_zero (hf x (hz x hx).1)
      (hz x hx).2 hdx (ne_of_gt (hcurv x (hz x hx).1 hdx)))
  · have hord : ∀ x ∈ z, vanishingOrder f x = 1 := by
      intro x hx
      rw [vanishingOrder_eq (hf x (hz x hx).1)]
      exact order_eq_one_of_deriv_ne_zero (hf x (hz x hx).1) (hz x hx).2
        (fun he => hstat ⟨x, hx, he⟩)
    obtain ⟨u, v, huv⟩ := ZeroCounting.exists_pair_covers_zeros htwo
    have hsub : z ⊆ {u, v} := by
      intro x hx
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        huv x (hz x hx).1 (hz x hx).2
    have hcard : z.card ≤ 2 := (Finset.card_le_card hsub).trans Finset.card_le_two
    calc
      ∑ x ∈ z, vanishingOrder f x = ∑ _x ∈ z, (1 : ENat) :=
        Finset.sum_congr rfl hord
      _ = (z.card : ENat) := by simp
      _ ≤ 2 := by exact_mod_cast hcard

theorem multiplicityBound_one_of_deriv_pos_at_zeros {f : ℝ → ℝ} {a b : ℝ}
    (hf : AnalyticOnNhd ℝ f (Ioo a b))
    (hd : ∀ x ∈ Ioo a b, f x = 0 → 0 < deriv f x) :
    MultiplicityBound 1 f (Ioo a b) := by
  classical
  have hc := ZeroOrientation.atMostOneZeroOn_Ioo_of_deriv_pos_at_zeros
    (fun x hx => (hf x hx).differentiableAt.differentiableWithinAt) hd
  intro z hz
  have hcard : z.card ≤ 1 := Finset.card_le_one.mpr (by
    intro x hx y hy
    exact hc (hz x hx).1 (hz y hy).1 (hz x hx).2 (hz y hy).2)
  have ho : ∀ x ∈ z, vanishingOrder f x = 1 := by
    intro x hx
    rw [vanishingOrder_eq (hf x (hz x hx).1)]
    exact order_eq_one_of_deriv_ne_zero (hf x (hz x hx).1) (hz x hx).2
      (ne_of_gt (hd x (hz x hx).1 (hz x hx).2))
  calc
    ∑ x ∈ z, vanishingOrder f x = ∑ _x ∈ z, (1 : ENat) := Finset.sum_congr rfl ho
    _ = (z.card : ENat) := by simp
    _ ≤ 1 := by exact_mod_cast hcard

theorem multiplicityBound_of_zero_order_transport {f g : ℝ → ℝ} {s t : Set ℝ} {n : ℕ}
    (hg : MultiplicityBound n g t)
    (hmap : ∀ x ∈ s, f x = 0 → x ∈ t ∧ g x = 0 ∧
      vanishingOrder f x = vanishingOrder g x) :
    MultiplicityBound n f s := by
  intro z hz
  have hb := hg z (fun x hx =>
    ⟨(hmap x (hz x hx).1 (hz x hx).2).1, (hmap x (hz x hx).1 (hz x hx).2).2.1⟩)
  have he : ∑ x ∈ z, vanishingOrder f x = ∑ x ∈ z, vanishingOrder g x :=
    Finset.sum_congr rfl fun x hx => (hmap x (hz x hx).1 (hz x hx).2).2.2
  rwa [he]

end LeanVerification.AnalyticMultiplicity
