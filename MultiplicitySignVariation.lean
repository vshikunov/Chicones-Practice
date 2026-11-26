import LeanVerification.CountedZeros
import LeanVerification.FiniteZeroCounting

/-!
# From actual analytic multiplicities to strict sign variation

Finite sums of the actual vanishing orders bound the cardinality of every
finite zero set. The checked IVT construction between opposite-sign samples
then gives the sign-variation bound for every natural-number bound. A finite
multiplicity bound also excludes vanishing on every nonempty open subset.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace LeanVerification.AnalyticMultiplicity
set_option maxHeartbeats 500000

theorem MultiplicityBound.card_zeros_le {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hb : MultiplicityBound n f s) (hf : AnalyticOnNhd ℝ f s)
    (z : Finset ℝ) (hz : ∀ x∈z,x∈s ∧ f x=0) : z.card≤n := by
  have hsum : (z.card : ENat)≤∑ x∈z,vanishingOrder f x := by
    calc
      (z.card : ENat)=∑ _x∈z,(1 : ENat) := by simp
      _ ≤ _ := Finset.sum_le_sum fun x hx =>
        one_le_vanishingOrder_of_zero (hf x (hz x hx).1) (hz x hx).2
  exact_mod_cast hsum.trans (hb z hz)

theorem MultiplicityBound.atMostZeros {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hb : MultiplicityBound n f s) (hf : AnalyticOnNhd ℝ f s) :
    FiniteZeroCounting.AtMostZeros n f s := by
  classical
  rintro ⟨x,hx,hz⟩
  let z := Finset.univ.image x
  have hcard : z.card=n+1 := by
    rw [Finset.card_image_of_injective _ hx.injective]
    simp
  have hbound : z.card≤n := hb.card_zeros_le hf z (by
    intro y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    exact hz i)
  omega

/-- Opposite-sign samples create distinct interior zeros; each actual
analytic vanishing order is at least one. No open-set assumption is needed
for this convex-domain implication. -/
theorem MultiplicityBound.atMostStrictSignChanges {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hb : MultiplicityBound n f s) (hs : Convex ℝ s) (hf : AnalyticOnNhd ℝ f s) :
    SignVariation.AtMostStrictSignChanges n f s :=
  FiniteZeroCounting.atMostStrictSignChanges_of_zero_bound hs hf.continuousOn
    (hb.atMostZeros hf)

/-- A zero function on a nonempty open subset has an infinite-order germ.
Such a germ contradicts even the singleton instance of a finite bound. -/
theorem MultiplicityBound.exists_nonzero_on_open {f : ℝ → ℝ} {s t : Set ℝ} {n : ℕ}
    (hb : MultiplicityBound n f s) (hf : AnalyticOnNhd ℝ f s)
    (ht : IsOpen t) (hne : t.Nonempty) (hts : t⊆s) :
    ∃ x∈t,f x≠0 := by
  classical
  by_contra hn
  push_neg at hn
  obtain ⟨x,hx⟩ := hne
  have ha := hf x (hts hx)
  have he : f =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [ht.mem_nhds hx] with y hy
    exact hn y hy
  have ho : vanishingOrder f x=⊤ := by
    rw [vanishingOrder_eq ha]
    exact ha.order_eq_top_iff.mpr he
  have hbound := hb {x} (by
    intro y hy
    have hyx : y=x := Finset.mem_singleton.mp hy
    subst y
    exact ⟨hts hx,hn x hx⟩)
  simp only [Finset.sum_singleton,ho] at hbound
  simp at hbound

theorem MultiplicityBound.exists_nonzero_Ioo {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {a b : ℝ}
    (hb : MultiplicityBound n f s) (hf : AnalyticOnNhd ℝ f s)
    (hab : a<b) (hsub : Ioo a b⊆s) : ∃ x∈Ioo a b,f x≠0 :=
  hb.exists_nonzero_on_open hf isOpen_Ioo (nonempty_Ioo.mpr hab) hsub

end LeanVerification.AnalyticMultiplicity
