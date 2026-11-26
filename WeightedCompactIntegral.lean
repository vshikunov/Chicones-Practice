import LeanVerification.WeightedAnalyticIntegral

/-!
# Integrable weights and compact real analytic integration

The common series and its majorant are constructed from actual joint kernel
analyticity near the compact integration set. The scalar weight is any integrable
real function; its endpoint behavior needs no continuity assumption.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal

namespace LeanVerification.WeightedCompactIntegral

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def periodParameterEmbedding : E →L[ℝ] (E × ℝ) :=
  (ContinuousLinearMap.id ℝ E).prod 0

theorem periodParameterEmbedding_apply (y : E) :
    periodParameterEmbedding y = (y, 0) := rfl

theorem norm_periodParameterEmbedding_apply (y : E) :
    ‖periodParameterEmbedding y‖ = ‖y‖ := by
  simp [periodParameterEmbedding, Prod.norm_def]

theorem norm_periodParameterEmbedding_le : ‖periodParameterEmbedding (E := E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  simp only [norm_periodParameterEmbedding_apply, one_mul, le_refl]

def angularSeriesMajorant
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ)
    (a : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  ∑' s : Σ l : ℕ, {s : Finset (Fin (n + l)) // s.card = l},
    ‖p (n + s.1)‖₊ * a ^ s.1

theorem summable_angularSeriesMajorant
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ)
    {a b : ℝ≥0} (hab : (a + b : ℝ≥0∞) < p.radius) :
    Summable (fun n => angularSeriesMajorant p a n * b ^ n) := by
  simpa only [angularSeriesMajorant, ← NNReal.tsum_mul_right] using
    (NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hab)).2

theorem nnnorm_shiftedSeries_le_majorant
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ)
    {a : ℝ≥0} (ha : (a : ℝ≥0∞) < p.radius)
    {z : (E × ℝ)} (hz : ‖z‖₊ ≤ a) (n : ℕ) :
    ‖p.changeOrigin z n‖₊ ≤ angularSeriesMajorant p a n := by
  have hzr : (‖z‖₊ : ℝ≥0∞) < p.radius :=
    (ENNReal.coe_le_coe.mpr hz).trans_lt ha
  refine (p.nnnorm_changeOrigin_le n hzr).trans ?_
  apply Summable.tsum_le_tsum
  · intro s
    exact mul_le_mul_left' (pow_le_pow_left' hz _) _
  · exact p.changeOriginSeries_summable_aux₂ hzr n
  · exact p.changeOriginSeries_summable_aux₂ ha n

def localAngularSeries
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ)
    (t₀ t : ℝ) : FormalMultilinearSeries ℝ E ℝ := fun n =>
  (p.changeOrigin (0, t - t₀) n).compContinuousLinearMap
    (fun _ : Fin n => periodParameterEmbedding)

theorem norm_localAngularSeries_le_majorant
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ)
    {a : ℝ≥0} (ha : (a : ℝ≥0∞) < p.radius)
    {t₀ t : ℝ} (ht : ‖t - t₀‖₊ ≤ a) (n : ℕ) :
    ‖localAngularSeries p t₀ t n‖ ≤ angularSeriesMajorant p a n := by
  have hz : ‖((0 : E), t - t₀)‖₊ ≤ a := by
    simpa only [Prod.nnnorm_def, nnnorm_zero, max_eq_right (zero_le _)] using ht
  have hb : ‖p.changeOrigin (0, t - t₀) n‖ ≤ (angularSeriesMajorant p a n : ℝ) := by
    exact_mod_cast nnnorm_shiftedSeries_le_majorant p ha hz n
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) norm_periodParameterEmbedding_le)).trans hb

theorem continuousOn_localAngularSeries
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ)
    {a : ℝ≥0} (ha : (a : ℝ≥0∞) < p.radius)
    (t₀ : ℝ) (n : ℕ) :
    ContinuousOn (fun t => localAngularSeries p t₀ t n)
      (Metric.closedBall t₀ a) := by
  intro t ht
  have hz : ((0 : E), t - t₀) ∈
      EMetric.ball 0 p.radius := by
    rw [mem_emetric_ball_zero_iff]
    have ht' : ‖t - t₀‖₊ ≤ a := by
      exact_mod_cast (mem_closedBall_iff_norm.mp ht)
    simpa only [enorm_eq_nnnorm, Prod.nnnorm_def, nnnorm_zero,
      max_eq_right (zero_le _)] using (ENNReal.coe_le_coe.mpr ht').trans_lt ha
  have hc := ((p.hasFPowerSeriesOnBall_changeOrigin n
    ((bot_le : (0 : ℝ≥0∞) ≤ a).trans_lt ha)).analyticAt_of_mem hz).continuousAt
  have htmap : ContinuousAt (fun u : ℝ => ((0 : E), u - t₀)) t := by
    fun_prop
  have hct : ContinuousAt (fun u : ℝ => p.changeOrigin (0, u - t₀) n) t :=
    hc.comp (f := fun u : ℝ => ((0 : E), u - t₀)) htmap
  exact ((ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin n => periodParameterEmbedding)).continuous.continuousAt.comp
      hct).continuousWithinAt

theorem integrableOn_localAngularSeries
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ)
    {a : ℝ≥0} (ha : (a : ℝ≥0∞) < p.radius)
    {t₀ : ℝ} {S : Set ℝ} (hS : S ⊆ Metric.closedBall t₀ a) (n : ℕ) :
    IntegrableOn (fun t => localAngularSeries p t₀ t n) S :=
  ((continuousOn_localAngularSeries p ha t₀ n).integrableOn_compact
    (isCompact_closedBall t₀ a)).mono_set hS


theorem hasFPowerSeriesOnBall_localWeightedIntegral
    {f : E × ℝ → ℝ} {p : FormalMultilinearSeries ℝ (E × ℝ) ℝ}
    {x₀ : E} {t₀ : ℝ} {R : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p (x₀, t₀) R)
    {a b : ℝ≥0} (hb : 0 < b) (hab : (a + b : ℝ≥0∞) < R)
    {S : Set ℝ} (hSm : MeasurableSet S) (hS : S ⊆ Metric.closedBall t₀ a)
    {ω : ℝ → ℝ} (hω : IntegrableOn ω S) :
    HasFPowerSeriesOnBall (fun x => ∫ t in S, ω t * f (x, t))
      (WeightedAnalyticIntegral.weightedSeries ω (localAngularSeries p t₀) (volume.restrict S))
      x₀ b := by
  have habp : (a + b : ℝ≥0∞) < p.radius := hab.trans_le hp.r_le
  have haR : (a : ℝ≥0∞) < R := (le_add_right le_rfl).trans_lt hab
  have ha : (a : ℝ≥0∞) < p.radius := haR.trans_le hp.r_le
  have hsum : Summable (fun n => (angularSeriesMajorant p a n : ℝ) * (b : ℝ) ^ n) := by
    simpa only [NNReal.coe_mul, NNReal.coe_pow] using
      NNReal.summable_coe.mpr (summable_angularSeriesMajorant p habp)
  have hbound (n : ℕ) : ∀ᵐ t ∂volume.restrict S,
      ‖localAngularSeries p t₀ t n‖ ≤ (angularSeriesMajorant p a n : ℝ) := by
    filter_upwards [ae_restrict_mem hSm] with t ht
    exact norm_localAngularSeries_le_majorant p ha
      (by exact_mod_cast (mem_closedBall_iff_norm.mp (hS ht))) n
  apply WeightedAnalyticIntegral.hasFPowerSeriesOnBall_weightedIntegral hb hω
    (fun n => (integrableOn_localAngularSeries p ha hS n).aestronglyMeasurable)
    hbound (fun n => (angularSeriesMajorant p a n).coe_nonneg) hsum
  intro y hyb
  have hlim : ∀ᵐ t ∂volume.restrict S,
      HasSum (fun n => localAngularSeries p t₀ t n (fun _ => y)) (f (x₀ + y, t)) := by
    filter_upwards [ae_restrict_mem hSm] with t ht
    have hshift : ‖((0 : E), t - t₀)‖₊ ≤ a := by
      simpa only [Prod.nnnorm_def, nnnorm_zero, max_eq_right (zero_le _)] using
        (show ‖t - t₀‖₊ ≤ a by exact_mod_cast (mem_closedBall_iff_norm.mp (hS ht)))
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
  exact hlim

theorem eventually_integrableOn_localWeighted_fiber
    {f : (E × ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (E × ℝ) ℝ}
    {x₀ : E} {t₀ : ℝ} {R : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p (x₀, t₀) R)
    {a b : ℝ≥0} (hb : 0 < b) (hab : (a + b : ℝ≥0∞) < R)
    {S : Set ℝ} (hSm : MeasurableSet S) (hS : S ⊆ Metric.closedBall t₀ a)
    {ω : ℝ → ℝ} (hω : IntegrableOn ω S) :
    ∀ᶠ x in 𝓝 x₀, IntegrableOn (fun t => ω t * f (x, t)) S := by
  have haR : (a : ℝ≥0∞) < R := (le_add_right le_rfl).trans_lt hab
  have hbR : (b : ℝ≥0∞) < R := (le_add_left le_rfl).trans_lt hab
  filter_upwards [Metric.ball_mem_nhds x₀ (show (0 : ℝ) < b from hb)] with x hx
  have hc : ContinuousOn (fun t => f (x, t)) (Metric.closedBall t₀ a) := by
    intro t ht
    have hxR : (‖x - x₀‖₊ : ℝ≥0∞) < R := by
      have hx' : ‖x - x₀‖₊ < b := by exact_mod_cast (mem_ball_iff_norm.mp hx)
      exact (ENNReal.coe_lt_coe.mpr hx').trans hbR
    have htR : (‖t - t₀‖₊ : ℝ≥0∞) < R := by
      have ht' : ‖t - t₀‖₊ ≤ a := by exact_mod_cast (mem_closedBall_iff_norm.mp ht)
      exact (ENNReal.coe_le_coe.mpr ht').trans_lt haR
    have hxt : (x, t) ∈ EMetric.ball (x₀, t₀) R := by
      rw [EMetric.mem_ball, edist_eq_enorm_sub, enorm_eq_nnnorm]
      change max (‖x - x₀‖₊ : ℝ≥0∞) (‖t - t₀‖₊ : ℝ≥0∞) < R
      exact max_lt hxR htR
    exact ((hp.analyticAt_of_mem hxt).continuousAt.comp
      (f := fun u : ℝ => (x, u)) (by fun_prop)).continuousWithinAt
  exact hω.mul_continuousOn_of_subset hc hSm (isCompact_closedBall t₀ a) hS


/-- Actual joint kernel analyticity constructs a weighted analytic integral
on every small measurable integration piece. -/
theorem exists_local_analytic_weighted_integral
    {f : E × ℝ → ℝ} {x₀ : E} {t₀ : ℝ}
    (hf : AnalyticAt ℝ f (x₀, t₀)) :
    ∃ a : ℝ, 0 < a ∧ ∀ S : Set ℝ, MeasurableSet S → S ⊆ Metric.ball t₀ a →
      ∀ ω : ℝ → ℝ, IntegrableOn ω S →
        AnalyticAt ℝ (fun x => ∫ t in S, ω t * f (x, t)) x₀ ∧
        ∀ᶠ x in 𝓝 x₀, IntegrableOn (fun t => ω t * f (x, t)) S := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨a, ha, haR⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hp.r_pos
  simp only [zero_add] at haR
  obtain ⟨b, hb, hab⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp haR
  refine ⟨a, ha, ?_⟩
  intro S hSm hS ω hω
  have hSc : S ⊆ Metric.closedBall t₀ a := hS.trans ball_subset_closedBall
  exact ⟨(hasFPowerSeriesOnBall_localWeightedIntegral hp hb hab hSm hSc hω).analyticAt,
    eventually_integrableOn_localWeighted_fiber hp hb hab hSm hSc hω⟩

/-- Finite measurable splitting combines the local weighted integrals while
retaining the integrability required by additivity. -/
theorem analytic_weighted_integral_of_finite_cover
    {ι : Type*} {f : E × ℝ → ℝ} {x₀ : E} {ω : ℝ → ℝ}
    (s : Finset ι) (U : ι → Set ℝ)
    (hUm : ∀ i, MeasurableSet (U i))
    (hU : ∀ i ∈ s, ∀ S : Set ℝ, MeasurableSet S → S ⊆ U i →
      IntegrableOn ω S →
      AnalyticAt ℝ (fun x => ∫ t in S, ω t * f (x, t)) x₀ ∧
      ∀ᶠ x in 𝓝 x₀, IntegrableOn (fun t => ω t * f (x, t)) S)
    {S : Set ℝ} (hSm : MeasurableSet S) (hS : S ⊆ ⋃ i ∈ s, U i)
    (hω : IntegrableOn ω S) :
    AnalyticAt ℝ (fun x => ∫ t in S, ω t * f (x, t)) x₀ ∧
      ∀ᶠ x in 𝓝 x₀, IntegrableOn (fun t => ω t * f (x, t)) S := by
  classical
  induction s using Finset.induction_on generalizing S with
  | empty =>
      have hSe : S = ∅ := subset_empty_iff.mp (by simpa using hS)
      subst S
      exact ⟨by simpa only [Measure.restrict_empty, integral_zero_measure] using
        (analyticAt_const : AnalyticAt ℝ (fun _ : E => (0 : ℝ)) x₀),
        Filter.Eventually.of_forall fun _ => integrableOn_empty⟩
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
        filter_upwards [hA.2, hB.2] with x hxA hxB
        simpa only [inter_union_diff] using hxA.union hxB
      refine ⟨(hA.1.add hB.1).congr ?_, hInt⟩
      filter_upwards [hInt] with x hx
      exact integral_inter_add_diff (hUm i) hx

/-- Joint analyticity of the actual kernel near a compact integration set
implies joint analyticity of its integral against any integrable real weight. -/
theorem analyticAt_weightedIntegral_of_joint_on_compact
    {f : E × ℝ → ℝ} {x₀ : E} {ω : ℝ → ℝ}
    {K S : Set ℝ} (hK : IsCompact K)
    (hf : ∀ t ∈ K, AnalyticAt ℝ f (x₀, t))
    (hSm : MeasurableSet S) (hSK : S ⊆ K) (hω : IntegrableOn ω S) :
    AnalyticAt ℝ (fun x => ∫ t in S, ω t * f (x, t)) x₀ ∧
      ∀ᶠ x in 𝓝 x₀, IntegrableOn (fun t => ω t * f (x, t)) S := by
  classical
  choose a ha hlocal using
    (fun t : K => exists_local_analytic_weighted_integral (hf t t.property))
  let U : K → Set ℝ := fun t => Metric.ball t (a t)
  have hcover : K ⊆ ⋃ t : K, U t := by
    intro t ht
    exact mem_iUnion.mpr ⟨⟨t, ht⟩, mem_ball_self (ha ⟨t, ht⟩)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U (fun _ => isOpen_ball) hcover
  exact analytic_weighted_integral_of_finite_cover s U
    (fun _ => isOpen_ball.measurableSet)
    (fun t _ S hSm hSt hωS => hlocal t S hSm hSt ω hωS) hSm (hSK.trans hs) hω

end LeanVerification.WeightedCompactIntegral
