import LeanVerification.RealComplexification

/-!
# Uniqueness on real slices and compatibility of complexified real germs

The one-variable identity theorem is applied successively in each coordinate.
This proves agreement on intersections of complex balls with real centers.
-/

noncomputable section
open Set Filter Metric Complex
open scoped Topology ENNReal NNReal

namespace LeanVerification.RealComplexification
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- Holomorphic functions on an open connected planar set that agree on its
real slice agree everywhere, provided the real slice is nonempty. -/
theorem eqOn_of_eqOn_real_slice
    {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsOpen U) (hc : IsPreconnected U) {r : ℝ} (hr : (r : ℂ) ∈ U)
    (he : ∀ x : ℝ, (x : ℂ) ∈ U → f x = g x) : EqOn f g U := by
  apply hf.eqOn_of_preconnected_of_mem_closure hg hc hr
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hr)
  let d : ℝ := min ε δ / 2
  have hd : 0 < d := half_pos (lt_min hε hδ)
  have hdε : d < ε := (half_lt_self (lt_min hε hδ)).trans_le (min_le_left _ _)
  have hdδ : d < δ := (half_lt_self (lt_min hε hδ)).trans_le (min_le_right _ _)
  have hdist : dist ((r+d : ℝ) : ℂ) (r : ℂ) = d := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real]
    simp only [add_sub_cancel_left, Real.norm_eq_abs, abs_of_pos hd]
  refine ⟨((r+d : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · exact he (r+d) (hsub (by simpa only [mem_ball, hdist] using hdδ))
  · simp only [mem_singleton_iff]
    intro h
    have h' : r+d=r := Complex.ofReal_injective h
    linarith
  · rw [dist_comm, hdist]
    exact hdε

def complexProduct {n : ℕ} (S : Fin n → Set ℂ) : Set (CVec n) :=
  {z | ∀ i, z i ∈ S i}

/-- Successive one-variable uniqueness proves the several-variable real-slice
identity principle on arbitrary products of connected open planar sets. -/
theorem eqOn_product_of_eqOn_real_slice {n : ℕ}
    (S : Fin n → Set ℂ) (hS : ∀ i, IsOpen (S i))
    (hc : ∀ i, IsPreconnected (S i)) (hr : ∀ i, ∃ r : ℝ, (r : ℂ) ∈ S i)
    {f g : CVec n → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexProduct S))
    (hg : AnalyticOnNhd ℂ g (complexProduct S))
    (he : ∀ x : RVec n, embed x ∈ complexProduct S → f (embed x) = g (embed x)) :
    EqOn f g (complexProduct S) := by
  induction n with
  | zero =>
      intro z hz
      have hez : embed (fun i : Fin 0 => Fin.elim0 i) = z := by
        ext i
        exact Fin.elim0 i
      simpa only [hez] using he (fun i : Fin 0 => Fin.elim0 i) (by simpa only [hez] using hz)
  | succ n ih =>
      intro z hz
      let S' : Fin n → Set ℂ := fun i => S i.succ
      have htail : Fin.tail z ∈ complexProduct S' := fun i => hz i.succ
      have hfixed (r : ℝ) (hr₀ : (r : ℂ) ∈ S 0) :
          f (Fin.cons (r : ℂ) (Fin.tail z)) = g (Fin.cons (r : ℂ) (Fin.tail z)) := by
        have hmap (w : CVec n) :
            AnalyticAt ℂ (fun t : CVec n => (Fin.cons (r : ℂ) t : CVec (n+1))) w := by
          apply AnalyticAt.pi
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact analyticAt_const
          · exact ((ContinuousLinearMap.proj (R := ℂ) j : CVec n →L[ℂ] ℂ).analyticAt w)
        have hm (w : CVec n) (hw : w ∈ complexProduct S') :
            Fin.cons (r : ℂ) w ∈ complexProduct S := by
          intro i
          refine Fin.cases hr₀ (fun j => hw j) i
        have hfa : AnalyticOnNhd ℂ (fun w : CVec n => f (Fin.cons (r : ℂ) w))
            (complexProduct S') := by
          intro w hw
          exact (hf _ (hm w hw)).comp_of_eq (hmap w) rfl
        have hga : AnalyticOnNhd ℂ (fun w : CVec n => g (Fin.cons (r : ℂ) w))
            (complexProduct S') := by
          intro w hw
          exact (hg _ (hm w hw)).comp_of_eq (hmap w) rfl
        apply ih S' (fun i => hS i.succ) (fun i => hc i.succ) (fun i => hr i.succ)
          hfa hga ?_ htail
        intro x hx
        have hcons : embed (Fin.cons r x) = Fin.cons (r : ℂ) (embed x) := by
          ext i
          exact Fin.cases rfl (fun _ => rfl) i
        simpa only [hcons] using he (Fin.cons r x) (by rw [hcons]; exact hm _ hx)
      have hmap (w : ℂ) :
          AnalyticAt ℂ (fun u : ℂ => (Fin.cons u (Fin.tail z) : CVec (n+1))) w := by
        apply AnalyticAt.pi
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact analyticAt_id
        · exact analyticAt_const
      have hm (w : ℂ) (hw : w ∈ S 0) : Fin.cons w (Fin.tail z) ∈ complexProduct S := by
        intro i
        exact Fin.cases hw (fun j => hz j.succ) i
      have hfa : AnalyticOnNhd ℂ (fun w : ℂ => f (Fin.cons w (Fin.tail z))) (S 0) := by
        intro w hw
        exact (hf _ (hm w hw)).comp_of_eq (hmap w) rfl
      have hga : AnalyticOnNhd ℂ (fun w : ℂ => g (Fin.cons w (Fin.tail z))) (S 0) := by
        intro w hw
        exact (hg _ (hm w hw)).comp_of_eq (hmap w) rfl
      obtain ⟨r, hr₀⟩ := hr 0
      have hez := eqOn_of_eqOn_real_slice hfa hga (hS 0) (hc 0) hr₀ hfixed (hz 0)
      simpa only [Fin.cons_self_tail] using hez

/-- Real-centered complex balls have compatible holomorphic extensions when
the extensions agree with one real function on their respective real sections. -/
theorem eqOn_inter_real_centered_balls {n : ℕ}
    {f g : CVec n → ℂ} {q : RVec n → ℂ} {a b : RVec n} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hf : AnalyticOnNhd ℂ f (ball (embed a) r))
    (hg : AnalyticOnNhd ℂ g (ball (embed b) s))
    (hfr : ∀ x ∈ ball a r, f (embed x) = q x)
    (hgr : ∀ x ∈ ball b s, g (embed x) = q x) :
    EqOn f g (ball (embed a) r ∩ ball (embed b) s) := by
  intro z hz
  let S : Fin n → Set ℂ := fun i => ball ((a i : ℝ) : ℂ) r ∩ ball ((b i : ℝ) : ℂ) s
  have hprod : complexProduct S = ball (embed a) r ∩ ball (embed b) s := by
    ext w
    simp only [complexProduct, S, mem_setOf_eq, mem_inter_iff, mem_ball,
      dist_pi_lt_iff hr, dist_pi_lt_iff hs, embed_apply]
    exact forall_and
  have hopen : ∀ i, IsOpen (S i) := fun _ => isOpen_ball.inter isOpen_ball
  have hconn : ∀ i, IsPreconnected (S i) := fun i =>
    ((convex_ball ((a i : ℝ) : ℂ) r).inter (convex_ball ((b i : ℝ) : ℂ) s)).isPreconnected
  have hre : ∀ i, ∃ u : ℝ, (u : ℂ) ∈ S i := by
    intro i
    refine ⟨(z i).re, ?_, ?_⟩
    · have hz' : dist (z i) ((a i : ℝ) : ℂ) < r :=
        (dist_pi_lt_iff hr).mp hz.1 i
      have hd : dist (((z i).re : ℝ) : ℂ) ((a i : ℝ) : ℂ) ≤
          dist (z i) ((a i : ℝ) : ℂ) := by
        rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, dist_eq_norm]
        simpa only [Complex.sub_re, ofReal_re] using
          Complex.abs_re_le_norm (z i - ((a i : ℝ) : ℂ))
      exact hd.trans_lt hz'
    · have hz' : dist (z i) ((b i : ℝ) : ℂ) < s :=
        (dist_pi_lt_iff hs).mp hz.2 i
      have hd : dist (((z i).re : ℝ) : ℂ) ((b i : ℝ) : ℂ) ≤
          dist (z i) ((b i : ℝ) : ℂ) := by
        rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, dist_eq_norm]
        simpa only [Complex.sub_re, ofReal_re] using
          Complex.abs_re_le_norm (z i - ((b i : ℝ) : ℂ))
      exact hd.trans_lt hz'
  have hf' : AnalyticOnNhd ℂ f (complexProduct S) := by
    rw [hprod]
    exact hf.mono inter_subset_left
  have hg' : AnalyticOnNhd ℂ g (complexProduct S) := by
    rw [hprod]
    exact hg.mono inter_subset_right
  apply eqOn_product_of_eqOn_real_slice S hopen hconn hre hf' hg' ?_ (by rw [hprod]; exact hz)
  intro x hx
  rw [hprod] at hx
  have hxr : x ∈ ball a r := by
    simpa only [mem_ball_iff_norm, ← embed_sub, norm_embed] using hx.1
  have hxs : x ∈ ball b s := by
    simpa only [mem_ball_iff_norm, ← embed_sub, norm_embed] using hx.2
  exact (hfr x hxr).trans (hgr x hxs).symm

end LeanVerification.RealComplexification
