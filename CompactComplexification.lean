import LeanVerification.RealSliceUniqueness

/-!
# Single holomorphic extension near a compact real set

Actual locally complexified series agree on every overlap by real-slice
uniqueness. Their glued extension is holomorphic on an open neighborhood of the
real set. Compactness then supplies a uniform closed complex neighborhood and
one bound on it.
-/

noncomputable section
open Set Filter Metric Complex
open scoped Topology ENNReal NNReal

namespace LeanVerification.RealComplexification
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- Real analytic germs on any real set glue to one holomorphic extension on
an open complex neighborhood of that set. Agreement holds on the entire real
section of the constructed complex domain. -/
theorem exists_holomorphic_extension_near_real_set {m : ℕ}
    {f : RVec m → ℂ} {K : Set (RVec m)}
    (hf : ∀ x ∈ K, AnalyticAt ℝ f x) :
    ∃ U : Set (CVec m), ∃ F : CVec m → ℂ,
      IsOpen U ∧ embed '' K ⊆ U ∧ AnalyticOnNhd ℂ F U ∧
      ∀ x : RVec m, embed x ∈ U → F (embed x) = f x := by
  classical
  choose G ε hε hGa hEq using
    (fun x : K => exists_local_holomorphic_extension (hf x x.property))
  let U : Set (CVec m) := ⋃ x : K, ball (embed x.val) (ε x)
  let F : CVec m → ℂ := fun z =>
    if hz : z ∈ U then G (Classical.choose (mem_iUnion.mp hz)) z else 0
  have hFeq (x : K) (z : CVec m) (hz : z ∈ ball (embed x.val) (ε x)) : F z = G x z := by
    have hzU : z ∈ U := mem_iUnion.mpr ⟨x, hz⟩
    dsimp only [F]
    rw [dif_pos hzU]
    let y : K := Classical.choose (mem_iUnion.mp hzU)
    have hy : z ∈ ball (embed y.val) (ε y) := Classical.choose_spec (mem_iUnion.mp hzU)
    exact eqOn_inter_real_centered_balls (hε y) (hε x) (hGa y) (hGa x) (hEq y) (hEq x)
      ⟨hy, hz⟩
  refine ⟨U, F, isOpen_iUnion (fun _ => isOpen_ball), ?_, ?_, ?_⟩
  · rintro z ⟨x, hx, rfl⟩
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hε ⟨x, hx⟩)⟩
  · intro z hz
    obtain ⟨x, hx⟩ := mem_iUnion.mp hz
    apply (hGa x z hx).congr
    filter_upwards [isOpen_ball.mem_nhds hx] with w hw
    exact (hFeq x w hw).symm
  · intro x hx
    obtain ⟨y, hy⟩ := mem_iUnion.mp hx
    rw [hFeq y (embed x) hy]
    apply hEq y x
    simpa only [mem_ball_iff_norm, ← embed_sub, norm_embed] using hy

/-- Compact real analytic data admit one bounded holomorphic extension on a
uniform closed complex neighborhood. Both the extension and its bound are
constructed, not assumed. -/
theorem exists_bounded_holomorphic_extension_near_compact {m : ℕ}
    {f : RVec m → ℂ} {K : Set (RVec m)} (hK : IsCompact K)
    (hf : ∀ x ∈ K, AnalyticAt ℝ f x) :
    ∃ U : Set (CVec m), ∃ F : CVec m → ℂ, ∃ δ C : ℝ,
      IsOpen U ∧ 0 < δ ∧ 0 < C ∧ cthickening δ (embed '' K) ⊆ U ∧
      AnalyticOnNhd ℂ F U ∧ (∀ z ∈ cthickening δ (embed '' K), ‖F z‖ ≤ C) ∧
      (∀ x : RVec m, embed x ∈ U → F (embed x) = f x) := by
  obtain ⟨U, F, hU, hKU, hFa, hEq⟩ := exists_holomorphic_extension_near_real_set hf
  have hKe : IsCompact (embed '' K) := hK.image embedCLM.continuous
  obtain ⟨δ, hδ, hsub⟩ := hKe.exists_cthickening_subset_open hU hKU
  obtain ⟨M, hM⟩ := hKe.cthickening.exists_bound_of_continuousOn (hFa.continuousOn.mono hsub)
  refine ⟨U, F, δ, |M|+1, hU, hδ, by positivity, hsub, hFa, ?_, hEq⟩
  intro z hz
  exact (hM z hz).trans (by linarith [le_abs_self M])

/-- Real-valued data are covered by the same construction through the canonical
real-to-complex embedding of the function values. -/
theorem exists_bounded_holomorphic_extension_real_valued {m : ℕ}
    {f : RVec m → ℝ} {K : Set (RVec m)} (hK : IsCompact K)
    (hf : ∀ x ∈ K, AnalyticAt ℝ f x) :
    ∃ U : Set (CVec m), ∃ F : CVec m → ℂ, ∃ δ C : ℝ,
      IsOpen U ∧ 0 < δ ∧ 0 < C ∧ cthickening δ (embed '' K) ⊆ U ∧
      AnalyticOnNhd ℂ F U ∧ (∀ z ∈ cthickening δ (embed '' K), ‖F z‖ ≤ C) ∧
      (∀ x : RVec m, embed x ∈ U → F (embed x) = (f x : ℂ)) := by
  exact exists_bounded_holomorphic_extension_near_compact hK
    (fun x hx => Complex.ofRealCLM.analyticAt _ |>.comp (hf x hx))

end LeanVerification.RealComplexification
