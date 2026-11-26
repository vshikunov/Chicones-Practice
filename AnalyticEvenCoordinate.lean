import LeanVerification.AnalyticEvenDescent
import LeanVerification.Loud.JointMorse

/-!
# An analytic spatial coordinate at an even turn

Two even analytic germs descend through the square coordinate. A nonzero
second derivative of the spatial germ makes its descended first derivative
nonzero, so the analytic inverse theorem produces the spatial germ.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace LeanVerification.AnalyticEvenCoordinate

set_option maxHeartbeats 800000

theorem second_deriv_comp_square {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0) :
    deriv (deriv (fun δ : ℝ => g (δ ^ 2))) 0 = 2 * deriv g 0 := by
  have he : deriv (fun δ : ℝ => g (δ ^ 2)) =ᶠ[𝓝 (0 : ℝ)]
      fun δ => 2 * δ * deriv g (δ ^ 2) := by
    have hsq : ContinuousAt (fun δ : ℝ => δ ^ 2) 0 := continuousAt_id.pow 2
    have hga : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), AnalyticAt ℝ g (δ ^ 2) := by
      have hh : ∀ᶠ q : ℝ in 𝓝 ((0 : ℝ) ^ 2), AnalyticAt ℝ g q := by
        simpa using hg.eventually_analyticAt
      exact hsq.eventually hh
    filter_upwards [hga] with δ hδ
    have hd := hδ.differentiableAt.hasDerivAt.comp (h := fun x : ℝ => x ^ 2)
      δ ((hasDerivAt_id δ).pow 2)
    simpa only [Function.comp_def, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using hd.deriv
  have hgd : HasDerivAt (fun δ : ℝ => deriv g (δ ^ 2)) 0 0 := by
    have hgd₀ : HasDerivAt (deriv g) (deriv (deriv g) 0) ((0 : ℝ) ^ 2) := by
      simpa using hg.deriv.differentiableAt.hasDerivAt
    convert hgd₀.comp (h := fun x : ℝ => x ^ 2) 0 ((hasDerivAt_id (0 : ℝ)).pow 2)
      using 1 <;> simp
  have hd := (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul hgd)
  have hd' := hd.congr_of_eventuallyEq he
  simpa using hd'.deriv

theorem exists_analytic_spatial_germ
    {f z : ℝ × ℝ → ℝ} {r₀ : ℝ}
    (hf : AnalyticAt ℝ f (r₀, 0)) (hz : AnalyticAt ℝ z (r₀, 0))
    (hfe : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0), f (p.1, -p.2) = f p)
    (hze : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0), z (p.1, -p.2) = z p)
    (hz₂ : deriv (deriv (fun δ : ℝ => z (r₀, δ))) 0 ≠ 0) :
    ∃ F : ℝ × ℝ → ℝ, AnalyticAt ℝ F (r₀, z (r₀, 0)) ∧
      ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0), F (p.1, z p) = f p := by
  obtain ⟨f₀, hf₀, hfd⟩ := AnalyticEvenDescent.exists_analytic_even_descent hf hfe
  obtain ⟨z₀, hz₀, hzd⟩ := AnalyticEvenDescent.exists_analytic_even_descent hz hze
  have hzcenter : z₀ (r₀, 0) = z (r₀, 0) := by
    simpa using hzd.self_of_nhds
  have hzv : AnalyticAt ℝ (fun q : ℝ => z₀ (r₀, q)) 0 :=
    hz₀.comp_of_eq (f := fun q : ℝ => (r₀, q))
      (analyticAt_const.prod analyticAt_id) rfl
  have hzds : (fun δ : ℝ => z₀ (r₀, δ ^ 2)) =ᶠ[𝓝 (0 : ℝ)]
      fun δ => z (r₀, δ) := by
    exact (continuousAt_const.prodMk continuousAt_id).eventually hzd
  have hvn : deriv (fun q : ℝ => z₀ (r₀, q)) 0 ≠ 0 := by
    intro hv0
    apply hz₂
    rw [← hzds.deriv.deriv_eq, second_deriv_comp_square hzv, hv0, mul_zero]
  let g : (ℝ × ℝ) × ℝ → ℝ := fun p => z₀ (p.1.1, p.2)
  let G : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ := fun p => (p.1, g p)
  let p₀ : (ℝ × ℝ) × ℝ := ((r₀, 0), 0)
  have hg : AnalyticAt ℝ g p₀ := hz₀.comp_of_eq
    (f := fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.2))
    ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd) rfl
  let l := fderiv ℝ g p₀
  have hv : l ((0, 0), 1) = deriv (fun q : ℝ => z₀ (r₀, q)) 0 := by
    have hp : HasDerivAt (fun q : ℝ => ((r₀, (0 : ℝ)), q)) ((0, 0), 1) 0 :=
      (hasDerivAt_const (0 : ℝ) (r₀, (0 : ℝ))).prodMk (hasDerivAt_id 0)
    exact (hg.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hp).unique
      hzv.differentiableAt.hasDerivAt
  let L := (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).prod l
  have hL : Function.Bijective L := Loud.triangular_linear_bijective l (hv ▸ hvn)
  let e := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hL.1) (LinearMap.range_eq_top.mpr hL.2)
  have he : HasStrictFDerivAt G (e : ((ℝ × ℝ) × ℝ) →L[ℝ] ((ℝ × ℝ) × ℝ)) p₀ := by
    have hh := hasStrictFDerivAt_fst.prodMk hg.hasStrictFDerivAt
    simpa only [G, e, ContinuousLinearEquiv.coe_ofBijective] using hh
  let I := he.localInverse G _ _
  have hG : AnalyticAt ℝ G p₀ := analyticAt_fst.prod hg
  have hI : AnalyticAt ℝ I (G p₀) :=
    (he.toPartialHomeomorph G).analyticAt_symm' he.mem_toPartialHomeomorph_source
      hG he.hasFDerivAt.fderiv
  let F : ℝ × ℝ → ℝ := fun p => f₀ ((I ((p.1, 0), p.2)).1.1,
    (I ((p.1, 0), p.2)).2)
  refine ⟨F, ?_, ?_⟩
  · have hm : AnalyticAt ℝ (fun p : ℝ × ℝ => ((p.1, (0 : ℝ)), p.2))
        (r₀, z (r₀, 0)) :=
      (analyticAt_fst.prod analyticAt_const).prod analyticAt_snd
    have hm0 : ((r₀, (0 : ℝ)), z (r₀, 0)) = G p₀ := by
      simp only [G, g, p₀, hzcenter]
    have hic := hI.comp_of_eq (f := fun p : ℝ × ℝ => ((p.1, (0 : ℝ)), p.2)) hm hm0
    have hif : AnalyticAt ℝ (fun p : ℝ × ℝ =>
        ((I ((p.1, 0), p.2)).1.1, (I ((p.1, 0), p.2)).2)) (r₀, z (r₀, 0)) :=
      ((analyticAt_fst.comp analyticAt_fst).comp hic).prod (analyticAt_snd.comp hic)
    apply hf₀.comp_of_eq (f := fun p : ℝ × ℝ =>
      ((I ((p.1, 0), p.2)).1.1, (I ((p.1, 0), p.2)).2)) hif
    have hi0 : I ((r₀, 0), z (r₀, 0)) = p₀ := by
      rw [hm0]
      exact he.localInverse_apply_image
    simp only [hi0, p₀]
  · have hm : ContinuousAt (fun p : ℝ × ℝ => ((p.1, (0 : ℝ)), p.2 ^ 2)) (r₀, 0) :=
      (continuousAt_fst.prodMk continuousAt_const).prodMk (continuousAt_snd.pow 2)
    have hli : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, 0),
        I (G ((p.1, 0), p.2 ^ 2)) = ((p.1, 0), p.2 ^ 2) := by
      have hh : ∀ᶠ q in 𝓝 (((r₀, (0 : ℝ)), (0 : ℝ) ^ 2)), I (G q) = q := by
        simpa only [zero_pow two_ne_zero] using he.eventually_left_inverse
      exact hm.eventually hh
    filter_upwards [hfd, hzd, hli] with p hfp hzp hip
    dsimp only [F]
    have hh : I ((p.1, 0), z p) = ((p.1, 0), p.2 ^ 2) := by
      rw [← hzp]
      exact hip
    rw [hh]
    exact hfp

end LeanVerification.AnalyticEvenCoordinate
