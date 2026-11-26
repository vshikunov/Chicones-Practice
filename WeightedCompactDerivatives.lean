import LeanVerification.WeightedCompactIntegral
import LeanVerification.AnalyticDerivativeBounds

/-!
# All mixed derivatives of the actual weighted compact integral

The coefficient, integrability, and differentiation hypotheses are derived from
joint real analyticity near the compact integration set, at every base parameter.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal

namespace LeanVerification.WeightedCompactIntegral

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasFPowerSeriesOnBall_localAngularSeries
    {f : E × ℝ → ℝ} {p : FormalMultilinearSeries ℝ (E × ℝ) ℝ}
    {x₀ : E} {t₀ : ℝ} {R : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p (x₀, t₀) R)
    {a b : ℝ≥0} (hb : 0 < b) (hab : (a + b : ℝ≥0∞) < R)
    {t : ℝ} (ht : t ∈ closedBall t₀ a) :
    HasFPowerSeriesOnBall (fun x => f (x, t)) (localAngularSeries p t₀ t) x₀ b := by
  have habp : (a + b : ℝ≥0∞) < p.radius := hab.trans_le hp.r_le
  have haR : (a : ℝ≥0∞) < R := (le_add_right le_rfl).trans_lt hab
  have ha : (a : ℝ≥0∞) < p.radius := haR.trans_le hp.r_le
  have hsum : Summable (fun n => (angularSeriesMajorant p a n : ℝ) * (b : ℝ) ^ n) := by
    simpa only [NNReal.coe_mul, NNReal.coe_pow] using
      NNReal.summable_coe.mpr (summable_angularSeriesMajorant p habp)
  refine ⟨?_, ENNReal.coe_pos.mpr hb, ?_⟩
  · apply FormalMultilinearSeries.le_radius_of_summable_norm
    exact Summable.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg b.coe_nonneg _))
      (fun n => mul_le_mul_of_nonneg_right
        (norm_localAngularSeries_le_majorant p ha
          (by exact_mod_cast (mem_closedBall_iff_norm.mp ht)) n)
        (pow_nonneg b.coe_nonneg _)) hsum
  · intro y hy
    have hyb : ‖y‖₊ < b := ENNReal.coe_lt_coe.mp (mem_emetric_ball_zero_iff.mp hy)
    have hshift : ‖((0 : E), t - t₀)‖₊ ≤ a := by
      simpa only [Prod.nnnorm_def, nnnorm_zero, max_eq_right (zero_le _)] using
        (show ‖t - t₀‖₊ ≤ a by exact_mod_cast (mem_closedBall_iff_norm.mp ht))
    have hshiftR : (‖((0 : E), t - t₀)‖₊ : ℝ≥0∞) < R :=
      (ENNReal.coe_le_coe.mpr hshift).trans_lt haR
    have hyshift : periodParameterEmbedding y ∈ EMetric.ball 0
        (R - ‖((0 : E), t - t₀)‖₊) := by
      rw [mem_emetric_ball_zero_iff, lt_tsub_iff_right]
      have hemb : ‖periodParameterEmbedding y‖₊ = ‖y‖₊ := by
        apply Subtype.ext
        exact norm_periodParameterEmbedding_apply y
      rw [enorm_eq_nnnorm, hemb]
      calc
        (‖y‖₊ : ℝ≥0∞) + ‖((0 : E), t - t₀)‖₊ ≤ b + a :=
          add_le_add (ENNReal.coe_le_coe.mpr hyb.le) (ENNReal.coe_le_coe.mpr hshift)
        _ = a + b := add_comm _ _
        _ < R := hab
    have htseries := (hp.changeOrigin hshiftR).hasSum hyshift
    have heqt : t₀ + (t - t₀) = t := by ring
    simpa only [localAngularSeries, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      periodParameterEmbedding_apply, Prod.mk_add_mk, add_zero, zero_add,
      heqt] using htseries


theorem weightedIntegral_local_all_derivatives
    {f : E × ℝ → ℝ} {p : FormalMultilinearSeries ℝ (E × ℝ) ℝ}
    {x₀ : E} {t₀ : ℝ} {R : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p (x₀, t₀) R)
    {a b : ℝ≥0} (hb : 0 < b) (hab : (a + b : ℝ≥0∞) < R)
    {S : Set ℝ} (hSm : MeasurableSet S) (hS : S ⊆ closedBall t₀ a)
    {ω : ℝ → ℝ} (hω : IntegrableOn ω S) (n : ℕ) (v : Fin n → E) :
    IntegrableOn (fun t => ω t * iteratedFDeriv ℝ n (fun x => f (x, t)) x₀ v) S ∧
    iteratedFDeriv ℝ n (fun x => ∫ t in S, ω t * f (x, t)) x₀ v =
      ∫ t in S, ω t * iteratedFDeriv ℝ n (fun x => f (x, t)) x₀ v := by
  classical
  have habp : (a + b : ℝ≥0∞) < p.radius := hab.trans_le hp.r_le
  have ha : (a : ℝ≥0∞) < p.radius := (le_add_right le_rfl).trans_lt habp
  have hsum : Summable (fun n => (angularSeriesMajorant p a n : ℝ) * (b : ℝ) ^ n) := by
    simpa only [NNReal.coe_mul, NNReal.coe_pow] using
      NNReal.summable_coe.mpr (summable_angularSeriesMajorant p habp)
  have hm (n : ℕ) : AEStronglyMeasurable (fun t => localAngularSeries p t₀ t n)
      (volume.restrict S) := (integrableOn_localAngularSeries p ha hS n).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ t ∂volume.restrict S,
      ‖localAngularSeries p t₀ t n‖ ≤ (angularSeriesMajorant p a n : ℝ) := by
    filter_upwards [ae_restrict_mem hSm] with t ht
    exact norm_localAngularSeries_le_majorant p ha
      (by exact_mod_cast (mem_closedBall_iff_norm.mp (hS ht))) n
  have hseries : ∀ᵐ t ∂volume.restrict S,
      HasFPowerSeriesOnBall (fun x => f (x, t)) (localAngularSeries p t₀ t) x₀ b := by
    filter_upwards [ae_restrict_mem hSm] with t ht
    exact hasFPowerSeriesOnBall_localAngularSeries hp hb hab (hS ht)
  refine ⟨?_, WeightedAnalyticIntegral.iteratedFDeriv_weightedIntegral hb hω hm hbound
    (fun n => (angularSeriesMajorant p a n).coe_nonneg) hsum hseries n v⟩
  have hsumint : Integrable
      (fun t => ∑ σ : Equiv.Perm (Fin n),
        ω t * localAngularSeries p t₀ t n (fun i => v (σ i))) (volume.restrict S) := by
    apply integrable_finset_sum
    intro σ _
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℝ
      (fun i => v (σ i))).integrable_comp
        (WeightedAnalyticIntegral.integrable_weightedCoefficient hω hm hbound n))
  apply hsumint.congr
  filter_upwards [hseries] with t ht
  rw [ht.iteratedFDeriv_eq_sum_of_completeSpace v, Finset.mul_sum]

theorem exists_local_weighted_integral_all_derivatives
    {f : E × ℝ → ℝ} {x₀ : E} {t₀ : ℝ}
    (hf : AnalyticAt ℝ f (x₀, t₀)) :
    ∃ a : ℝ, 0 < a ∧ ∀ S : Set ℝ, MeasurableSet S → S ⊆ ball t₀ a →
      ∀ ω : ℝ → ℝ, IntegrableOn ω S →
        AnalyticAt ℝ (fun x => ∫ t in S, ω t * f (x, t)) x₀ ∧
        (∀ᶠ x in 𝓝 x₀, IntegrableOn (fun t => ω t * f (x, t)) S) ∧
        ∀ n : ℕ, ∀ v : Fin n → E,
          IntegrableOn (fun t => ω t * iteratedFDeriv ℝ n (fun x => f (x, t)) x₀ v) S ∧
          iteratedFDeriv ℝ n (fun x => ∫ t in S, ω t * f (x, t)) x₀ v =
            ∫ t in S, ω t * iteratedFDeriv ℝ n (fun x => f (x, t)) x₀ v := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨a, ha, haR⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hp.r_pos
  simp only [zero_add] at haR
  obtain ⟨b, hb, hab⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp haR
  refine ⟨a, ha, ?_⟩
  intro S hSm hS ω hω
  have hSc : S ⊆ closedBall t₀ a := hS.trans ball_subset_closedBall
  exact ⟨(hasFPowerSeriesOnBall_localWeightedIntegral hp hb hab hSm hSc hω).analyticAt,
    eventually_integrableOn_localWeighted_fiber hp hb hab hSm hSc hω,
    fun n v => weightedIntegral_local_all_derivatives hp hb hab hSm hSc hω n v⟩

theorem iteratedFDeriv_eq_of_eventuallyEq {f g : E → ℝ} {x₀ : E}
    (he : f =ᶠ[𝓝 x₀] g) (n : ℕ) :
    iteratedFDeriv ℝ n f x₀ = iteratedFDeriv ℝ n g x₀ := by
  have heu : f =ᶠ[𝓝[univ] x₀] g := by simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ] using heu.iteratedFDerivWithin_eq he.eq_of_nhds n

theorem weighted_integral_all_derivatives_of_finite_cover
    {ι : Type*} {f : E × ℝ → ℝ} {x₀ : E} {ω : ℝ → ℝ}
    (s : Finset ι) (U : ι → Set ℝ)
    (hUm : ∀ i, MeasurableSet (U i))
    (hU : ∀ i ∈ s, ∀ S : Set ℝ, MeasurableSet S → S ⊆ U i → IntegrableOn ω S →
      AnalyticAt ℝ (fun x => ∫ t in S, ω t * f (x, t)) x₀ ∧
      (∀ᶠ x in 𝓝 x₀, IntegrableOn (fun t => ω t * f (x, t)) S) ∧
      ∀ n : ℕ, ∀ v : Fin n → E,
        IntegrableOn (fun t => ω t * iteratedFDeriv ℝ n (fun x => f (x, t)) x₀ v) S ∧
        iteratedFDeriv ℝ n (fun x => ∫ t in S, ω t * f (x, t)) x₀ v =
          ∫ t in S, ω t * iteratedFDeriv ℝ n (fun x => f (x, t)) x₀ v)
    {S : Set ℝ} (hSm : MeasurableSet S) (hS : S ⊆ ⋃ i ∈ s, U i)
    (hω : IntegrableOn ω S) :
    AnalyticAt ℝ (fun x => ∫ t in S, ω t * f (x, t)) x₀ ∧
      (∀ᶠ x in 𝓝 x₀, IntegrableOn (fun t => ω t * f (x, t)) S) ∧
      ∀ n : ℕ, ∀ v : Fin n → E,
        IntegrableOn (fun t => ω t * iteratedFDeriv ℝ n (fun x => f (x, t)) x₀ v) S ∧
        iteratedFDeriv ℝ n (fun x => ∫ t in S, ω t * f (x, t)) x₀ v =
          ∫ t in S, ω t * iteratedFDeriv ℝ n (fun x => f (x, t)) x₀ v := by
  classical
  induction s using Finset.induction_on generalizing S with
  | empty =>
      have hSe : S = ∅ := subset_empty_iff.mp (by simpa using hS)
      subst S
      refine ⟨by simpa only [Measure.restrict_empty, integral_zero_measure] using
        (analyticAt_const : AnalyticAt ℝ (fun _ : E => (0 : ℝ)) x₀),
        Filter.Eventually.of_forall fun _ => integrableOn_empty, ?_⟩
      intro n v
      refine ⟨integrableOn_empty, ?_⟩
      cases n with
      | zero => simp
      | succ n => simp only [Measure.restrict_empty, integral_zero_measure,
          iteratedFDeriv_succ_const, Pi.zero_apply, ContinuousMultilinearMap.zero_apply]
  | @insert i s his ih =>
      have hA := hU i (Finset.mem_insert_self i s) (S ∩ U i)
        (hSm.inter (hUm i)) inter_subset_right (hω.mono_set inter_subset_left)
      have hBsub : S \ U i ⊆ ⋃ j ∈ s, U j := by
        intro t ht
        have htcover := hS ht.1
        simp only [Finset.set_biUnion_insert] at htcover
        exact htcover.resolve_left ht.2
      have hB := ih (fun j hj => hU j (Finset.mem_insert_of_mem hj))
        (hSm.diff (hUm i)) hBsub (hω.mono_set diff_subset)
      have hInt : ∀ᶠ x in 𝓝 x₀, IntegrableOn (fun t => ω t * f (x, t)) S := by
        filter_upwards [hA.2.1, hB.2.1] with x hxA hxB
        simpa only [inter_union_diff] using hxA.union hxB
      have he : (fun x => (∫ t in S ∩ U i, ω t * f (x, t)) +
          ∫ t in S \ U i, ω t * f (x, t)) =ᶠ[𝓝 x₀]
          (fun x => ∫ t in S, ω t * f (x, t)) := by
        filter_upwards [hInt] with x hx
        exact integral_inter_add_diff (hUm i) hx
      refine ⟨(hA.1.add hB.1).congr he, hInt, ?_⟩
      intro n v
      have hAd := hA.2.2 n v
      have hBd := hB.2.2 n v
      have hId : IntegrableOn
          (fun t => ω t * iteratedFDeriv ℝ n (fun x => f (x, t)) x₀ v) S := by
        simpa only [inter_union_diff] using hAd.1.union hBd.1
      refine ⟨hId, ?_⟩
      rw [← iteratedFDeriv_eq_of_eventuallyEq he n,
        iteratedFDeriv_add_apply' hA.1.contDiffAt hB.1.contDiffAt,
        ContinuousMultilinearMap.add_apply, hAd.2, hBd.2]
      exact integral_inter_add_diff (hUm i) hId

/-- Every order of parameter differentiation passes under an integral with an
arbitrary integrable real weight when the kernel is jointly analytic near the
compact integration set. Both integrability and analyticity are conclusions. -/
theorem weightedIntegral_all_derivatives_on_compact
    {f : E × ℝ → ℝ} {x₀ : E} {ω : ℝ → ℝ} {K S : Set ℝ}
    (hK : IsCompact K) (hf : ∀ t ∈ K, AnalyticAt ℝ f (x₀, t))
    (hSm : MeasurableSet S) (hSK : S ⊆ K) (hω : IntegrableOn ω S) :
    AnalyticAt ℝ (fun x => ∫ t in S, ω t * f (x, t)) x₀ ∧
      (∀ᶠ x in 𝓝 x₀, IntegrableOn (fun t => ω t * f (x, t)) S) ∧
      ∀ n : ℕ, ∀ v : Fin n → E,
        IntegrableOn (fun t => ω t * iteratedFDeriv ℝ n (fun x => f (x, t)) x₀ v) S ∧
        iteratedFDeriv ℝ n (fun x => ∫ t in S, ω t * f (x, t)) x₀ v =
          ∫ t in S, ω t * iteratedFDeriv ℝ n (fun x => f (x, t)) x₀ v := by
  classical
  choose a ha hlocal using
    (fun t : K => exists_local_weighted_integral_all_derivatives (hf t t.property))
  let U : K → Set ℝ := fun t => ball t (a t)
  have hcover : K ⊆ ⋃ t : K, U t := by
    intro t ht
    exact mem_iUnion.mpr ⟨⟨t, ht⟩, mem_ball_self (ha ⟨t, ht⟩)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U (fun _ => isOpen_ball) hcover
  exact weighted_integral_all_derivatives_of_finite_cover s U
    (fun _ => isOpen_ball.measurableSet)
    (fun t _ S hSm hSt hωS => hlocal t S hSm hSt ω hωS) hSm (hSK.trans hs) hω

/-- One common parameter neighborhood carries all derivative identities and one
factorial estimate for every order of the integrated weighted kernel. -/
theorem weightedIntegral_uniform_all_derivatives
    {f : E × ℝ → ℝ} {x₀ : E} {ω : ℝ → ℝ} {K S : Set ℝ}
    (hK : IsCompact K) (hf : ∀ t ∈ K, AnalyticAt ℝ f (x₀, t))
    (hSm : MeasurableSet S) (hSK : S ⊆ K) (hω : IntegrableOn ω S) :
    ∃ ε C L : ℝ, 0 < ε ∧ 0 < C ∧ 0 < L ∧ ∀ x ∈ ball x₀ ε,
      AnalyticAt ℝ (fun y => ∫ t in S, ω t * f (y, t)) x ∧
      ∀ n : ℕ, ∀ v : Fin n → E,
        IntegrableOn (fun t => ω t * iteratedFDeriv ℝ n (fun y => f (y, t)) x v) S ∧
        iteratedFDeriv ℝ n (fun y => ∫ t in S, ω t * f (y, t)) x v =
          (∫ t in S, ω t * iteratedFDeriv ℝ n (fun y => f (y, t)) x v) ∧
        ‖iteratedFDeriv ℝ n (fun y => ∫ t in S, ω t * f (y, t)) x v‖ ≤
          C * (n.factorial : ℝ) * L ^ n * ∏ i, ‖v i‖ := by
  have hI := weightedIntegral_all_derivatives_on_compact hK hf hSm hSK hω
  have hnear : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ K, AnalyticAt ℝ f (x, t) :=
    hK.eventually_forall_of_forall_eventually fun t ht => (hf t ht).eventually_analyticAt
  obtain ⟨a, ha, hba⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨b, C, L, hb, hC, hL, hbound⟩ :=
    AnalyticDerivativeBounds.exists_uniform_factorial_derivative_bound hI.1
  refine ⟨min a b, C, L, lt_min ha hb, hC, hL, ?_⟩
  intro x hx
  have hxa : x ∈ ball x₀ a := ball_subset_ball (min_le_left _ _) hx
  have hxb : x ∈ ball x₀ b := ball_subset_ball (min_le_right _ _) hx
  have hi := weightedIntegral_all_derivatives_on_compact hK (hba hxa) hSm hSK hω
  exact ⟨hi.1, fun n v => ⟨(hi.2.2 n v).1, (hi.2.2 n v).2, hbound x hxb n v⟩⟩

end LeanVerification.WeightedCompactIntegral
