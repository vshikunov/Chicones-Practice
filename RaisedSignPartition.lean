import LeanVerification.RaisedAbelSigns
import LeanVerification.SignVariation
import Mathlib.Data.Fin.Tuple.Basic

/-!
The finite-sample definition of sign variation implies the interval sign
partitions used in the raised-kernel argument. No partition is assumed.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace LeanVerification.RaisedAbel

theorem atMost_sign_changes_const_mul {g : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {q : ℝ}
    (h : SignVariation.AtMostStrictSignChanges n g s) (hq : q ≠ 0) :
    SignVariation.AtMostStrictSignChanges n (fun x => q * g x) s := by
  intro ⟨x, hx, hm, hn, ha⟩
  apply h
  refine ⟨x, hx, hm, fun i => (mul_ne_zero_iff.mp (hn i)).2, ?_⟩
  intro i
  have he : q * g (x i.castSucc) * (q * g (x i.succ)) =
      (q * q) * (g (x i.castSucc) * g (x i.succ)) := by ring
  have hh := ha i
  rw [he] at hh
  exact neg_of_mul_neg_right hh (mul_self_pos.mpr hq).le

theorem nonneg_on_closed_interval {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hg : ContinuousOn g (Icc a b))
    (h : ∀ x ∈ Ioo a b, 0 ≤ g x) : ∀ x ∈ Icc a b, 0 ≤ g x := by
  have he : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  intro x hx
  apply le_on_closure h continuousOn_const
    (show ContinuousOn g (closure (Ioo a b)) by simpa only [he] using hg)
  simpa only [he] using hx

theorem nonpos_on_closed_interval {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hg : ContinuousOn g (Icc a b))
    (h : ∀ x ∈ Ioo a b, g x ≤ 0) : ∀ x ∈ Icc a b, g x ≤ 0 := by
  have he : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  intro x hx
  apply le_on_closure h
    (show ContinuousOn g (closure (Ioo a b)) by simpa only [he] using hg)
    continuousOn_const
  simpa only [he] using hx

theorem forbid_four_sign_samples {g : ℝ → ℝ} {H w x y z : ℝ}
    (hb : SignVariation.AtMostStrictSignChanges 2 g (Ioo 0 H))
    (hw : 0 < w) (hwx : w < x) (hxy : x < y) (hyz : y < z) (hz : z < H)
    (gw : 0 < g w) (gx : g x < 0) (gy : 0 < g y) (gz : g z < 0) : False := by
  apply hb
  refine ⟨![w, x, y, z], ?_, ?_, ?_, ?_⟩
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> simp_all
  · intro i
    fin_cases i <;> dsimp <;> constructor <;> linarith
  · intro i
    fin_cases i <;> dsimp <;> linarith
  · intro i
    fin_cases i <;> dsimp <;> nlinarith [mul_neg_of_pos_of_neg gw gx,
      mul_neg_of_neg_of_pos gx gy, mul_neg_of_pos_of_neg gy gz]

theorem exists_positive_before {g : ℝ → ℝ} {d x : ℝ}
    (hd : 0 < d) (hx : 0 < x) (hp : ∀ v ∈ Ioo 0 d, 0 < g v) :
    ∃ w, 0 < w ∧ w < x ∧ 0 < g w := by
  refine ⟨min d x / 2, by positivity, ?_, hp _ ⟨by positivity, ?_⟩⟩
  · have h := min_le_right d x
    have hpos : 0 < min d x := lt_min hd hx
    linarith
  · have h := min_le_left d x
    have hpos : 0 < min d x := lt_min hd hx
    linarith

/-- For an initially positive continuous function, at most two finite-sample
sign changes give either a single sign block, two blocks, or three blocks.
All endpoints, including the center and the energy cap, are included. -/
theorem sign_partition_of_atMost_two {g : ℝ → ℝ} {H d : ℝ}
    (hg : ContinuousOn g (Icc 0 H)) (hd : d ∈ Ioo 0 H)
    (hp : ∀ v ∈ Ioo 0 d, 0 < g v)
    (hb : SignVariation.AtMostStrictSignChanges 2 g (Ioo 0 H)) :
    (∀ v ∈ Icc 0 H, 0 ≤ g v) ∨
    (∃ c ∈ Ioo 0 H, (∀ v ∈ Icc 0 c, 0 ≤ g v) ∧
      (∀ v ∈ Icc c H, g v ≤ 0)) ∨
    (∃ c₁ c₂, 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < H ∧
      (∀ v ∈ Icc 0 c₁, 0 ≤ g v) ∧
      (∀ v ∈ Icc c₁ c₂, g v ≤ 0) ∧ (∀ v ∈ Icc c₂ H, 0 ≤ g v)) := by
  classical
  by_cases hnegative : ∃ x ∈ Ioo 0 H, g x < 0
  swap
  · left
    apply nonneg_on_closed_interval (hd.1.trans hd.2) hg
    intro x hx
    exact le_of_not_gt (fun hh => hnegative ⟨x, hx, hh⟩)
  let N : Set ℝ := {x | x ∈ Ioo 0 H ∧ g x < 0}
  have hN : N.Nonempty := hnegative
  have hNl : BddBelow N := ⟨0, fun x hx => hx.1.1.le⟩
  have hNu : BddAbove N := ⟨H, fun x hx => hx.1.2.le⟩
  let c₁ := sInf N
  let c₂ := sSup N
  have hdc : d ≤ c₁ := le_csInf hN (by
    intro x hx
    by_contra hh
    exact (not_lt_of_ge (hp x ⟨hx.1.1, lt_of_not_ge hh⟩).le) hx.2)
  have hc₁ : 0 < c₁ := hd.1.trans_le hdc
  have hc₂H : c₂ ≤ H := csSup_le hN (fun x hx => hx.1.2.le)
  have hc₁H : c₁ < H := by
    obtain ⟨x, hx⟩ := hN
    exact (csInf_le hNl hx).trans_lt hx.1.2
  have hc₁₂ : c₁ < c₂ := by
    obtain ⟨x, hx⟩ := hN
    have he : ∀ᶠ y in 𝓝 x, y ∈ Ioo 0 H ∧ g y < 0 := by
      have hgc := (hg x (Ioo_subset_Icc_self hx.1)).continuousAt
        (Icc_mem_nhds hx.1.1 hx.1.2)
      filter_upwards [isOpen_Ioo.mem_nhds hx.1,
        hgc.eventually (Iio_mem_nhds hx.2)] with y hy hgy
      exact ⟨hy, hgy⟩
    have hxs : x < c₂ := by
      have hf : ∃ y ∈ N, x < y := by
        have ht : ∀ᶠ y in 𝓝[>] x, y ∈ N := he.filter_mono nhdsWithin_le_nhds
        obtain ⟨y, hy, hyx⟩ := (ht.and self_mem_nhdsWithin).exists
        exact ⟨y, hy, hyx⟩
      obtain ⟨z, hz, hxz⟩ := hf
      exact hxz.trans_le (le_csSup hNu hz)
    exact (csInf_le hNl hx).trans_lt hxs
  have hfirst : ∀ v ∈ Icc 0 c₁, 0 ≤ g v := by
    apply nonneg_on_closed_interval hc₁ (hg.mono (Icc_subset_Icc le_rfl hc₁H.le))
    intro v hv
    apply le_of_not_gt
    intro hh
    have hvN : v ∈ N := ⟨⟨hv.1, hv.2.trans hc₁H⟩, hh⟩
    exact (not_le_of_gt hv.2) (csInf_le hNl hvN)
  have hmiddle : ∀ v ∈ Icc c₁ c₂, g v ≤ 0 := by
    apply nonpos_on_closed_interval hc₁₂ (hg.mono (Icc_subset_Icc hc₁.le hc₂H))
    intro v hv
    apply le_of_not_gt
    intro hgv
    obtain ⟨x, hx, hxv⟩ := exists_lt_of_csInf_lt hN hv.1
    obtain ⟨z, hz, hvz⟩ := exists_lt_of_lt_csSup hN hv.2
    obtain ⟨w, hw, hwx, hgw⟩ := exists_positive_before hd.1 hx.1.1 hp
    exact forbid_four_sign_samples hb hw hwx hxv hvz hz.1.2 hgw hx.2 hgv hz.2
  rcases lt_or_eq_of_le hc₂H with hc₂H | hc₂H
  · right; right
    refine ⟨c₁, c₂, hc₁, hc₁₂, hc₂H, hfirst, hmiddle, ?_⟩
    apply nonneg_on_closed_interval hc₂H (hg.mono (Icc_subset_Icc (hc₁.le.trans hc₁₂.le) le_rfl))
    intro v hv
    apply le_of_not_gt
    intro hh
    have hvN : v ∈ N := ⟨⟨(hc₁.trans hc₁₂).trans hv.1, hv.2⟩, hh⟩
    exact (not_le_of_gt hv.1) (le_csSup hNu hvN)
  · right; left
    refine ⟨c₁, ⟨hc₁, hc₁H⟩, hfirst, ?_⟩
    simpa only [hc₂H] using hmiddle

theorem forbid_three_sign_samples {g : ℝ → ℝ} {H w x y : ℝ}
    (hb : SignVariation.AtMostStrictSignChanges 1 g (Ioo 0 H))
    (hw : 0 < w) (hwx : w < x) (hxy : x < y) (hy : y < H)
    (gw : 0 < g w) (gx : g x < 0) (gy : 0 < g y) : False := by
  apply hb
  refine ⟨![w, x, y], ?_, ?_, ?_, ?_⟩
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> simp_all
  · intro i
    fin_cases i <;> dsimp <;> constructor <;> linarith
  · intro i
    fin_cases i <;> dsimp <;> linarith
  · intro i
    fin_cases i <;> dsimp <;> nlinarith [mul_neg_of_pos_of_neg gw gx,
      mul_neg_of_neg_of_pos gx gy]

theorem sign_partition_of_atMost_one {g : ℝ → ℝ} {H d : ℝ}
    (hg : ContinuousOn g (Icc 0 H)) (hd : d ∈ Ioo 0 H)
    (hp : ∀ v ∈ Ioo 0 d, 0 < g v)
    (hb : SignVariation.AtMostStrictSignChanges 1 g (Ioo 0 H)) :
    (∀ v ∈ Icc 0 H, 0 ≤ g v) ∨
    (∃ c ∈ Ioo 0 H, (∀ v ∈ Icc 0 c, 0 ≤ g v) ∧
      (∀ v ∈ Icc c H, g v ≤ 0)) := by
  classical
  by_cases hnegative : ∃ x ∈ Ioo 0 H, g x < 0
  swap
  · left
    apply nonneg_on_closed_interval (hd.1.trans hd.2) hg
    intro x hx
    exact le_of_not_gt (fun hh => hnegative ⟨x, hx, hh⟩)
  let N : Set ℝ := {x | x ∈ Ioo 0 H ∧ g x < 0}
  have hN : N.Nonempty := hnegative
  have hNl : BddBelow N := ⟨0, fun x hx => hx.1.1.le⟩
  let c := sInf N
  have hdc : d ≤ c := le_csInf hN (by
    intro x hx
    by_contra hh
    exact (not_lt_of_ge (hp x ⟨hx.1.1, lt_of_not_ge hh⟩).le) hx.2)
  have hc : 0 < c := hd.1.trans_le hdc
  have hcH : c < H := by
    obtain ⟨x, hx⟩ := hN
    exact (csInf_le hNl hx).trans_lt hx.1.2
  right
  refine ⟨c, ⟨hc, hcH⟩, ?_, ?_⟩
  · apply nonneg_on_closed_interval hc (hg.mono (Icc_subset_Icc le_rfl hcH.le))
    intro v hv
    apply le_of_not_gt
    intro hh
    have hvN : v ∈ N := ⟨⟨hv.1, hv.2.trans hcH⟩, hh⟩
    exact (not_le_of_gt hv.2) (csInf_le hNl hvN)
  · apply nonpos_on_closed_interval hcH (hg.mono (Icc_subset_Icc hc.le le_rfl))
    intro v hv
    apply le_of_not_gt
    intro hgv
    obtain ⟨x, hx, hxv⟩ := exists_lt_of_csInf_lt hN hv.1
    obtain ⟨w, hw, hwx, hgw⟩ := exists_positive_before hd.1 hx.1.1 hp
    exact forbid_three_sign_samples hb hw hwx hxv hv.2 hgw hx.2 hgv

theorem nonneg_of_atMost_zero {g : ℝ → ℝ} {H d : ℝ}
    (hg : ContinuousOn g (Icc 0 H)) (hd : d ∈ Ioo 0 H)
    (hp : ∀ v ∈ Ioo 0 d, 0 < g v)
    (hb : SignVariation.AtMostStrictSignChanges 0 g (Ioo 0 H)) :
    ∀ v ∈ Icc 0 H, 0 ≤ g v := by
  apply nonneg_on_closed_interval (hd.1.trans hd.2) hg
  intro v hv
  apply le_of_not_gt
  intro hgv
  obtain ⟨w, hw, hwv, hgw⟩ := exists_positive_before hd.1 hv.1 hp
  apply hb
  refine ⟨![w, v], ?_, ?_, ?_, ?_⟩
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> simp_all
  · intro i
    fin_cases i <;> dsimp <;> constructor <;> linarith [hv.2]
  · intro i
    fin_cases i <;> dsimp <;> linarith
  · intro i
    fin_cases i <;> dsimp
    exact mul_neg_of_pos_of_neg hgw hgv

theorem raised_multiplicity_const_iff {g : ℝ → ℝ} {H q : ℝ} {n : ℕ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hq : q ≠ 0) :
    AnalyticMultiplicity.MultiplicityBound n (raised (fun v => q * g v)) (Ioo 0 H) ↔
      AnalyticMultiplicity.MultiplicityBound n (raised g) (Ioo 0 H) := by
  have he : raised (fun v => q * g v) = fun h => q * raised g h := by
    funext h
    exact raised_const_mul q g h
  rw [he]
  exact AnalyticMultiplicity.multiplicityBound_mul_nonvanishing_iff
    (fun h hh => analyticAt_raised hg (Ioo_subset_Icc_self hh))
    (fun _ _ => analyticAt_const) (fun _ _ => hq)

theorem multiplicityBound_of_nonnegative {g : ℝ → ℝ} {H : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H))
    (hpos : ∀ v ∈ Icc 0 H, 0 ≤ g v) (hnz : ∃ v ∈ Icc 0 H, g v ≠ 0) :
    AnalyticMultiplicity.MultiplicityBound 0 (raised g) (Ioo 0 H) := by
  apply AnalyticMultiplicity.MultiplicityBound.of_nonvanishing
  intro h hh
  exact (raised_pos_before_first_change hg hh hh.2.le hpos hnz).ne'

/-- The complete raised-kernel multiplicity theorem for zero, one, or two
strict sign changes, stated with the finite-witness sign-variation notion. -/
theorem multiplicityBound_of_atMost_sign_changes {g : ℝ → ℝ} {H : ℝ} {n : ℕ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hH : 0 < H) (hn : n ≤ 2)
    (hnz : ∃ v ∈ Icc 0 H, g v ≠ 0)
    (hb : SignVariation.AtMostStrictSignChanges n g (Ioo 0 H)) :
    AnalyticMultiplicity.MultiplicityBound n (raised g) (Ioo 0 H) := by
  obtain ⟨q, d, hq, hd, _, hp⟩ := exists_initial_strict_sign hg hH hnz
  have hq0 : q ≠ 0 := by rcases hq with rfl | rfl <;> norm_num
  let j : ℝ → ℝ := fun v => q * g v
  have hj : AnalyticOnNhd ℝ j (Icc 0 H) :=
    fun v hv => analyticAt_const.mul (hg v hv)
  have hjnz : ∃ v ∈ Icc 0 H, j v ≠ 0 := by
    obtain ⟨v, hv, hvn⟩ := hnz
    exact ⟨v, hv, mul_ne_zero hq0 hvn⟩
  have hbj : SignVariation.AtMostStrictSignChanges n j (Ioo 0 H) :=
    atMost_sign_changes_const_mul hb hq0
  apply (raised_multiplicity_const_iff hg hq0).mp
  change AnalyticMultiplicity.MultiplicityBound n (raised j) (Ioo 0 H)
  interval_cases n
  · exact multiplicityBound_of_nonnegative hj
      (nonneg_of_atMost_zero hj.continuousOn hd hp hbj) hjnz
  · rcases sign_partition_of_atMost_one hj.continuousOn hd hp hbj with hall | ⟨c, hc, hfirst, hlast⟩
    · exact (multiplicityBound_of_nonnegative hj hall hjnz).mono_bound (by omega)
    · exact multiplicityBound_one_of_two_sign_blocks hj hc.1 hfirst hlast hjnz
  · rcases sign_partition_of_atMost_two hj.continuousOn hd hp hbj with hall | htwo | hthree
    · exact (multiplicityBound_of_nonnegative hj hall hjnz).mono_bound (by omega)
    · obtain ⟨c, hc, hfirst, hlast⟩ := htwo
      exact (multiplicityBound_one_of_two_sign_blocks hj hc.1 hfirst hlast hjnz).mono_bound (by omega)
    · obtain ⟨c₁, c₂, hc₁, hc₁₂, _, hfirst, hmiddle, hlast⟩ := hthree
      exact multiplicityBound_two_of_three_sign_blocks hj hc₁ hc₁₂ hfirst hmiddle hlast hjnz

end LeanVerification.RaisedAbel
