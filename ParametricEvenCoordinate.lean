import LeanVerification.AnalyticEvenCoordinate

/-! Analytic turn-coordinate descent with an arbitrary finite tuple of parameters. -/
noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.ParametricEvenCoordinate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
set_option maxHeartbeats 1200000

theorem triangular_bijective (l : (E × ℝ) →L[ℝ] ℝ) (hd : l (0,1) ≠ 0) :
    Function.Bijective ((ContinuousLinearMap.fst ℝ E ℝ).prod l) := by
  have hv (t : ℝ) : l (0,t)=t*l (0,1) := by
    have he : ((0,t):E×ℝ)=t • ((0,1):E×ℝ) := by simp
    rw [he,map_smul]
    rfl
  have hs (p : E×ℝ) : l p=l (p.1,0)+p.2*l (0,1) := by
    have he : p=(p.1,0)+(0,p.2) := by simp
    conv_lhs => rw [he]
    rw [map_add,hv]
  constructor
  · intro p q hpq
    change (p.1,l p)=(q.1,l q) at hpq
    have hp := congrArg Prod.fst hpq
    have hl := congrArg Prod.snd hpq
    dsimp only at hp hl
    refine Prod.ext hp ?_
    rw [hs p,hs q,hp] at hl
    exact mul_right_cancel₀ hd (add_left_cancel hl)
  · intro p
    refine ⟨(p.1,(p.2-l (p.1,0))/l (0,1)),?_⟩
    change (p.1,l (p.1,(p.2-l (p.1,0))/l (0,1)))=p
    refine Prod.ext rfl ?_
    change l (p.1,(p.2-l (p.1,0))/l (0,1))=p.2
    rw [hs,div_mul_cancel₀ _ hd]
    ring

theorem exists_analytic_spatial_germ {f z : E×ℝ→ℝ} {x₀ : E}
    (hf : AnalyticAt ℝ f (x₀,0)) (hz : AnalyticAt ℝ z (x₀,0))
    (hfe : ∀ᶠ p in 𝓝 (x₀,(0:ℝ)), f (p.1,-p.2)=f p)
    (hze : ∀ᶠ p in 𝓝 (x₀,(0:ℝ)), z (p.1,-p.2)=z p)
    (hz₂ : deriv (deriv (fun δ:ℝ=>z (x₀,δ))) 0 ≠ 0) :
    ∃ F : E×ℝ→ℝ, AnalyticAt ℝ F (x₀,z (x₀,0)) ∧
      ∀ᶠ p in 𝓝 (x₀,(0:ℝ)), F (p.1,z p)=f p := by
  obtain ⟨f₀,hf₀,hfd⟩ := AnalyticEvenDescent.exists_analytic_even_descent hf hfe
  obtain ⟨z₀,hz₀,hzd⟩ := AnalyticEvenDescent.exists_analytic_even_descent hz hze
  have hzcenter : z₀ (x₀,0)=z (x₀,0) := by simpa using hzd.self_of_nhds
  have hzv : AnalyticAt ℝ (fun q:ℝ=>z₀ (x₀,q)) 0 := hz₀.curry_right
  have hzds : (fun δ:ℝ=>z₀ (x₀,δ^2)) =ᶠ[𝓝 (0:ℝ)] fun δ=>z (x₀,δ) :=
    (continuousAt_const.prodMk continuousAt_id).eventually hzd
  have hvn : deriv (fun q:ℝ=>z₀ (x₀,q)) 0 ≠ 0 := by
    intro hv0
    apply hz₂
    rw [←hzds.deriv.deriv_eq,AnalyticEvenCoordinate.second_deriv_comp_square hzv,hv0,mul_zero]
  let G : E×ℝ→E×ℝ := fun p=>(p.1,z₀ p)
  let l := fderiv ℝ z₀ (x₀,0)
  have hv : l (0,1)=deriv (fun q:ℝ=>z₀ (x₀,q)) 0 := by
    have hp : HasDerivAt (fun q:ℝ=>(x₀,q)) (0,1) 0 :=
      (hasDerivAt_const (0:ℝ) x₀).prodMk (hasDerivAt_id 0)
    exact (hz₀.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hp).unique hzv.differentiableAt.hasDerivAt
  let L := (ContinuousLinearMap.fst ℝ E ℝ).prod l
  have hL : Function.Bijective L := triangular_bijective l (hv ▸ hvn)
  let e := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hL.1) (LinearMap.range_eq_top.mpr hL.2)
  have he : HasStrictFDerivAt G (e : E×ℝ→L[ℝ] E×ℝ) (x₀,0) := by
    simpa only [G,e,ContinuousLinearEquiv.coe_ofBijective] using
      hasStrictFDerivAt_fst.prodMk hz₀.hasStrictFDerivAt
  let I := he.localInverse G _ _
  have hG : AnalyticAt ℝ G (x₀,0) := analyticAt_fst.prod hz₀
  have hI : AnalyticAt ℝ I (G (x₀,0)) :=
    (he.toPartialHomeomorph G).analyticAt_symm' he.mem_toPartialHomeomorph_source
      hG he.hasFDerivAt.fderiv
  let F : E×ℝ→ℝ := f₀ ∘ I
  have hm0 : (x₀,z (x₀,0))=G (x₀,0) := by simp only [G,hzcenter]
  have hF : AnalyticAt ℝ F (x₀,z (x₀,0)) := by
    rw [hm0]
    exact hf₀.comp_of_eq hI he.localInverse_apply_image
  refine ⟨F,hF,?_⟩
  have hm : ContinuousAt (fun p:E×ℝ=>(p.1,p.2^2)) (x₀,0) :=
    continuousAt_fst.prodMk (continuousAt_snd.pow 2)
  have hli : ∀ᶠ p in 𝓝 (x₀,(0:ℝ)), I (G (p.1,p.2^2))=(p.1,p.2^2) := by
    have hh : ∀ᶠ q in 𝓝 (x₀,(0:ℝ)^2), I (G q)=q := by
      simpa using he.eventually_left_inverse
    exact hm.eventually hh
  filter_upwards [hfd,hzd,hli] with p hfp hzp hip
  change f₀ (I (p.1,z p))=f p
  rw [←hzp]
  change f₀ (I (G (p.1,p.2^2)))=f p
  rw [hip,hfp]

end LeanVerification.ParametricEvenCoordinate
