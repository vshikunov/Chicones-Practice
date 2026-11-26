import LeanVerification.WeightedCompactDerivatives
import LeanVerification.BanachAnalyticBounds

/-!
# Complex weights and outputs for the actual real analytic compact integral

The real and imaginary parts reduce the complex weighted kernel to four actual
real weighted kernels. Bounded real-linear maps and addition preserve all
integrability and mixed derivative identities.
-/

noncomputable section
open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal NNReal

namespace LeanVerification.ComplexWeightedRealIntegral
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {E F G Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [MeasurableSpace Ω]

def IntegralAnalyticAt (k : E → Ω → F) (μ : Measure Ω) (x₀ : E) : Prop :=
  (∀ᵐ t ∂μ, AnalyticAt ℝ (fun x => k x t) x₀) ∧
  AnalyticAt ℝ (fun x => ∫ t, k x t ∂μ) x₀ ∧
  (∀ᶠ x in 𝓝 x₀, Integrable (k x) μ) ∧
  ∀ n : ℕ, ∀ v : Fin n → E,
    Integrable (fun t => iteratedFDeriv ℝ n (fun x => k x t) x₀ v) μ ∧
    iteratedFDeriv ℝ n (fun x => ∫ t, k x t ∂μ) x₀ v =
      ∫ t, iteratedFDeriv ℝ n (fun x => k x t) x₀ v ∂μ

omit [CompleteSpace F] in
theorem iterated_eq_of_eventuallyEq {f g : E → F} {x : E}
    (he : f =ᶠ[𝓝 x] g) (n : ℕ) : iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  have heu : f =ᶠ[𝓝[univ] x] g := by simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ] using heu.iteratedFDerivWithin_eq he.eq_of_nhds n

omit [CompleteSpace G] in
theorem iterated_map {f : E → F} {x : E} (hf : AnalyticAt ℝ f x)
    (L : F →L[ℝ] G) (n : ℕ) (v : Fin n → E) :
    iteratedFDeriv ℝ n (fun y => L (f y)) x v = L (iteratedFDeriv ℝ n f x v) := by
  have he := L.iteratedFDeriv_comp_left
    (hf.contDiffAt : ContDiffAt ℝ (n : WithTop ℕ∞) f x) (le_refl (n : WithTop ℕ∞))
  exact congrArg (fun p : E[×n]→L[ℝ] G => p v) he

theorem IntegralAnalyticAt.map {k : E → Ω → F} {μ : Measure Ω} {x₀ : E}
    (hk : IntegralAnalyticAt k μ x₀) (L : F →L[ℝ] G) :
    IntegralAnalyticAt (fun x t => L (k x t)) μ x₀ := by
  have he : (fun x => ∫ t, L (k x t) ∂μ) =ᶠ[𝓝 x₀]
      (fun x => L (∫ t, k x t ∂μ)) := by
    filter_upwards [hk.2.2.1] with x hx
    exact L.integral_comp_comm hx
  refine ⟨hk.1.mono (fun t ht => (L.analyticAt _).comp ht),
    ((L.analyticAt _).comp hk.2.1).congr he.symm,
    hk.2.2.1.mono (fun x hx => L.integrable_comp hx), ?_⟩
  intro n v
  have hed : (fun t => iteratedFDeriv ℝ n (fun x => L (k x t)) x₀ v) =ᵐ[μ]
      (fun t => L (iteratedFDeriv ℝ n (fun x => k x t) x₀ v)) :=
    hk.1.mono (fun t ht => iterated_map ht L n v)
  refine ⟨(L.integrable_comp (hk.2.2.2 n v).1).congr hed.symm, ?_⟩
  rw [iterated_eq_of_eventuallyEq he n, iterated_map hk.2.1 L n v,
    (hk.2.2.2 n v).2, ← L.integral_comp_comm (hk.2.2.2 n v).1]
  exact integral_congr_ae hed.symm

theorem IntegralAnalyticAt.add {k l : E → Ω → F} {μ : Measure Ω} {x₀ : E}
    (hk : IntegralAnalyticAt k μ x₀) (hl : IntegralAnalyticAt l μ x₀) :
    IntegralAnalyticAt (fun x t => k x t + l x t) μ x₀ := by
  have he : (fun x => ∫ t, k x t + l x t ∂μ) =ᶠ[𝓝 x₀]
      (fun x => (∫ t, k x t ∂μ) + (∫ t, l x t ∂μ)) := by
    filter_upwards [hk.2.2.1, hl.2.2.1] with x hx hy
    exact integral_add hx hy
  refine ⟨?_, (hk.2.1.add hl.2.1).congr he.symm, ?_, ?_⟩
  · filter_upwards [hk.1, hl.1] with t ht hu
    exact ht.add hu
  · filter_upwards [hk.2.2.1, hl.2.2.1] with x hx hy
    exact hx.add hy
  · intro n v
    have hed : (fun t => iteratedFDeriv ℝ n (fun x => k x t + l x t) x₀ v) =ᵐ[μ]
        (fun t => iteratedFDeriv ℝ n (fun x => k x t) x₀ v +
          iteratedFDeriv ℝ n (fun x => l x t) x₀ v) := by
      filter_upwards [hk.1, hl.1] with t ht hu
      rw [iteratedFDeriv_add_apply' (ht.contDiffAt (n := n)) (hu.contDiffAt (n := n))]
      rfl
    refine ⟨((hk.2.2.2 n v).1.add (hl.2.2.2 n v).1).congr hed.symm, ?_⟩
    rw [iterated_eq_of_eventuallyEq he n,
      iteratedFDeriv_add_apply' (hk.2.1.contDiffAt (n := n)) (hl.2.1.contDiffAt (n := n)),
      ContinuousMultilinearMap.add_apply, (hk.2.2.2 n v).2, (hl.2.2.2 n v).2,
      ← integral_add (hk.2.2.2 n v).1 (hl.2.2.2 n v).1]
    exact integral_congr_ae hed.symm

section Compact
variable {K S : Set ℝ} {x₀ : E}

theorem real_weighted_kernel {q : E × ℝ → ℝ} {w : ℝ → ℝ}
    (hK : IsCompact K) (hq : ∀ t ∈ K, AnalyticAt ℝ q (x₀, t))
    (hSm : MeasurableSet S) (hSK : S ⊆ K) (hw : IntegrableOn w S) :
    IntegralAnalyticAt (fun x t => w t * q (x,t)) (volume.restrict S) x₀ := by
  obtain ⟨ha, hi, hd⟩ := WeightedCompactIntegral.weightedIntegral_all_derivatives_on_compact
    hK hq hSm hSK hw
  have hqa : ∀ᵐ t ∂volume.restrict S, AnalyticAt ℝ (fun x => q (x,t)) x₀ := by
    filter_upwards [ae_restrict_mem hSm] with t ht
    exact (hq t (hSK ht)).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  refine ⟨hqa.mono (fun t ht => analyticAt_const.mul ht), ha, hi, ?_⟩
  intro n v
  have hed : (fun t => iteratedFDeriv ℝ n (fun x => w t * q (x,t)) x₀ v) =ᵐ[volume.restrict S]
      (fun t => w t * iteratedFDeriv ℝ n (fun x => q (x,t)) x₀ v) := by
    filter_upwards [hqa] with t ht
    exact iterated_map ht (w t • (1 : ℝ →L[ℝ] ℝ)) n v
  refine ⟨(hd n v).1.congr hed.symm, ?_⟩
  rw [(hd n v).2]
  exact integral_congr_ae hed.symm

/-- Arbitrary complex weights and complex-valued jointly real analytic kernels
have an actual analytic integral, with eventual integrability and every mixed
derivative passing under the integral. -/
theorem complex_weighted_real_integral {q : E × ℝ → ℂ} {ω : ℝ → ℂ}
    (hK : IsCompact K) (hq : ∀ t ∈ K, AnalyticAt ℝ q (x₀, t))
    (hSm : MeasurableSet S) (hSK : S ⊆ K) (hω : IntegrableOn ω S) :
    AnalyticAt ℝ (fun x => ∫ t in S, ω t * q (x,t)) x₀ ∧
    (∀ᶠ x in 𝓝 x₀, IntegrableOn (fun t => ω t * q (x,t)) S) ∧
    ∀ n : ℕ, ∀ v : Fin n → E,
      IntegrableOn (fun t => ω t * iteratedFDeriv ℝ n (fun x => q (x,t)) x₀ v) S ∧
      iteratedFDeriv ℝ n (fun x => ∫ t in S, ω t * q (x,t)) x₀ v =
        ∫ t in S, ω t * iteratedFDeriv ℝ n (fun x => q (x,t)) x₀ v := by
  have hqr : ∀ t ∈ K, AnalyticAt ℝ (fun p => (q p).re) (x₀,t) :=
    fun t ht => (Complex.reCLM.analyticAt _).comp (hq t ht)
  have hqi : ∀ t ∈ K, AnalyticAt ℝ (fun p => (q p).im) (x₀,t) :=
    fun t ht => (Complex.imCLM.analyticAt _).comp (hq t ht)
  have hrr := (real_weighted_kernel hK hqr hSm hSK hω.re).map Complex.ofRealCLM
  have hii := (real_weighted_kernel hK hqi hSm hSK hω.im).map Complex.ofRealCLM
  have hri := (real_weighted_kernel hK hqi hSm hSK hω.re).map Complex.ofRealCLM
  have hir := (real_weighted_kernel hK hqr hSm hSK hω.im).map Complex.ofRealCLM
  have hall := (hrr.add (hii.map (- (1 : ℂ →L[ℝ] ℂ)))).add
    ((hri.add hir).map (Complex.I • (1 : ℂ →L[ℝ] ℂ)))
  have he : (fun x t => Complex.ofRealCLM ((ω t).re * (q (x,t)).re) +
      (- (1 : ℂ →L[ℝ] ℂ)) (Complex.ofRealCLM ((ω t).im * (q (x,t)).im)) +
      (Complex.I • (1 : ℂ →L[ℝ] ℂ))
        (Complex.ofRealCLM ((ω t).re * (q (x,t)).im) +
         Complex.ofRealCLM ((ω t).im * (q (x,t)).re))) =
      (fun x t => ω t * q (x,t)) := by
    funext x t
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
  change IntegralAnalyticAt _ _ _ at hall
  change IntegralAnalyticAt (fun x t => Complex.ofRealCLM ((ω t).re * (q (x,t)).re) +
      (- (1 : ℂ →L[ℝ] ℂ)) (Complex.ofRealCLM ((ω t).im * (q (x,t)).im)) +
      (Complex.I • (1 : ℂ →L[ℝ] ℂ))
        (Complex.ofRealCLM ((ω t).re * (q (x,t)).im) +
         Complex.ofRealCLM ((ω t).im * (q (x,t)).re))) (volume.restrict S) x₀ at hall
  rw [he] at hall
  refine ⟨hall.2.1, hall.2.2.1, ?_⟩
  intro n v
  have hed : (fun t => iteratedFDeriv ℝ n (fun x => ω t * q (x,t)) x₀ v) =ᵐ[volume.restrict S]
      (fun t => ω t * iteratedFDeriv ℝ n (fun x => q (x,t)) x₀ v) := by
    filter_upwards [ae_restrict_mem hSm] with t ht
    have hqa := (hq t (hSK ht)).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    exact iterated_map hqa (ω t • (1 : ℂ →L[ℝ] ℂ)) n v
  exact ⟨(hall.2.2.2 n v).1.congr hed,
    (hall.2.2.2 n v).2.trans (integral_congr_ae hed)⟩

/-- A single neighborhood carries every mixed derivative identity and one
factorial bound for the actual complex-weighted real analytic integral. -/
theorem uniform_complex_weighted_real_integral {q : E × ℝ → ℂ} {ω : ℝ → ℂ}
    (hK : IsCompact K) (hq : ∀ t ∈ K, AnalyticAt ℝ q (x₀, t))
    (hSm : MeasurableSet S) (hSK : S ⊆ K) (hω : IntegrableOn ω S) :
    ∃ ε C L : ℝ, 0 < ε ∧ 0 < C ∧ 0 < L ∧ ∀ x ∈ ball x₀ ε,
      AnalyticAt ℝ (fun y => ∫ t in S, ω t * q (y,t)) x ∧
      ∀ n : ℕ, ∀ v : Fin n → E,
        IntegrableOn (fun t => ω t * iteratedFDeriv ℝ n (fun y => q (y,t)) x v) S ∧
        iteratedFDeriv ℝ n (fun y => ∫ t in S, ω t * q (y,t)) x v =
          ∫ t in S, ω t * iteratedFDeriv ℝ n (fun y => q (y,t)) x v ∧
        ‖iteratedFDeriv ℝ n (fun y => ∫ t in S, ω t * q (y,t)) x v‖ ≤
          C * (n.factorial : ℝ) * L^n * ∏ i, ‖v i‖ := by
  have hI := complex_weighted_real_integral hK hq hSm hSK hω
  have hnear : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ K, AnalyticAt ℝ q (x,t) :=
    hK.eventually_forall_of_forall_eventually fun t ht => (hq t ht).eventually_analyticAt
  obtain ⟨a, ha, hba⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨b, C, L, hb, hC, hL, hbound⟩ :=
    BanachAnalyticBounds.exists_uniform_factorial_derivative_bound hI.1
  refine ⟨min a b, C, L, lt_min ha hb, hC, hL, ?_⟩
  intro x hx
  have hxa : x ∈ ball x₀ a := ball_subset_ball (min_le_left _ _) hx
  have hxb : x ∈ ball x₀ b := ball_subset_ball (min_le_right _ _) hx
  have hi := complex_weighted_real_integral hK (hba hxa) hSm hSK hω
  exact ⟨hi.1, fun n v => ⟨(hi.2.2 n v).1, (hi.2.2 n v).2, hbound x hxb n v⟩⟩

end Compact
end LeanVerification.ComplexWeightedRealIntegral
