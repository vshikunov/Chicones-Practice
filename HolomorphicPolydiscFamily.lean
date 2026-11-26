import LeanVerification.PolydiscCauchy

/-!
# Joint holomorphy of compact continuous families in any finite dimension

The actual product Cauchy formula identifies the family with a Banach-valued
Cauchy transform. Its kernel is analytic in the Banach algebra of continuous
functions on the boundary torus; integration is a bounded linear map.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex ContinuousMap
open scoped Topology ENNReal NNReal

namespace LeanVerification.PolydiscCauchy

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ)

theorem isCompact_closedPolydisc : IsCompact (closedPolydisc c R) :=
  isCompact_pi_infinite fun i => isCompact_closedBall (c i) (R i)

theorem isCompact_distinguishedBoundary : IsCompact (distinguishedBoundary c R) :=
  isCompact_pi_infinite fun i => isCompact_sphere (c i) (R i)

instance boundaryCompactSpace : CompactSpace (distinguishedBoundary c R) :=
  isCompact_iff_compactSpace.mp (isCompact_distinguishedBoundary c R)

theorem isOpen_openPolydisc : IsOpen (openPolydisc c R) := by
  have he : openPolydisc c R = ⋂ i : Fin n, (fun z : Fin n → ℂ => z i) ⁻¹' ball (c i) (R i) := by
    ext z
    simp only [openPolydisc, mem_setOf_eq, mem_iInter, mem_preimage]
  rw [he]
  exact isOpen_iInter_of_finite fun i => isOpen_ball.preimage (continuous_apply i)

def torusParameter (hR : ∀ i, 0 ≤ R i) :
    C((Fin n → ℝ), distinguishedBoundary c R) :=
  ⟨fun θ => ⟨torusMap c R θ, torusMap_mem_boundary c hR θ⟩,
    (continuous_torusMap c R).subtype_mk _⟩

section ContourOperator

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

def boundaryExtension (g : C(distinguishedBoundary c R, V)) (z : Fin n → ℂ) : V := by
  classical
  exact if hz : z ∈ distinguishedBoundary c R then g ⟨z, hz⟩ else 0

omit [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] in
theorem boundaryExtension_apply (g : C(distinguishedBoundary c R, V))
    {z : Fin n → ℂ} (hz : z ∈ distinguishedBoundary c R) :
    boundaryExtension c R g z = g ⟨z, hz⟩ := by
  classical
  simp only [boundaryExtension, dif_pos hz]

omit [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] in
theorem torusIntegrable_boundaryExtension (hR : ∀ i, 0 ≤ R i)
    (g : C(distinguishedBoundary c R, V)) :
    TorusIntegrable (boundaryExtension c R g) c R := by
  have he : (fun θ => boundaryExtension c R g (torusMap c R θ)) =
      fun θ => g (torusParameter c R hR θ) := by
    funext θ
    exact boundaryExtension_apply c R g (torusMap_mem_boundary c hR θ)
  unfold TorusIntegrable
  rw [he]
  exact (g.continuous.comp (torusParameter c R hR).continuous).continuousOn.integrableOn_compact
    isCompact_Icc

def torusLinearMap (hR : ∀ i, 0 ≤ R i) : C(distinguishedBoundary c R, V) →ₗ[ℂ] V where
  toFun g := torusIntegral (boundaryExtension c R g) c R
  map_add' f g := by
    have he : boundaryExtension c R (f + g) =
        fun z => boundaryExtension c R f z + boundaryExtension c R g z := by
      classical
      funext z
      by_cases hz : z ∈ distinguishedBoundary c R <;> simp [boundaryExtension, hz]
    rw [he]
    exact torusIntegral_add (torusIntegrable_boundaryExtension c R hR f)
      (torusIntegrable_boundaryExtension c R hR g)
  map_smul' a g := by
    have he : boundaryExtension c R (a • g) = fun z => a • boundaryExtension c R g z := by
      classical
      funext z
      by_cases hz : z ∈ distinguishedBoundary c R <;> simp [boundaryExtension, hz]
    rw [he]
    exact torusIntegral_smul a _ _ _

def torusCLM (hR : ∀ i, 0 ≤ R i) : C(distinguishedBoundary c R, V) →L[ℂ] V :=
  (torusLinearMap c R hR).mkContinuous
    ((2 * Real.pi) ^ n * ∏ i, |R i|) (fun g => by
      apply norm_torusIntegral_le_of_norm_le_const
      intro θ
      rw [boundaryExtension_apply c R g (torusMap_mem_boundary c hR θ)]
      exact g.norm_coe_le_norm _)

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] in
theorem torusCLM_apply (hR : ∀ i, 0 ≤ R i) (g : C(distinguishedBoundary c R, V)) :
    torusCLM c R hR g = torusIntegral (boundaryExtension c R g) c R := rfl

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] in
theorem torusCLM_apply_of_eqOn (hR : ∀ i, 0 ≤ R i)
    (g : C(distinguishedBoundary c R, V)) (f : (Fin n → ℂ) → V)
    (he : ∀ z : distinguishedBoundary c R, g z = f z) :
    torusCLM c R hR g = torusIntegral f c R := by
  rw [torusCLM_apply]
  unfold torusIntegral
  congr 1
  funext θ
  rw [boundaryExtension_apply c R g (torusMap_mem_boundary c hR θ), he]

end ContourOperator

section Kernel

def constCLM : ℂ →L[ℂ] C(distinguishedBoundary c R, ℂ) where
  toFun := ContinuousMap.const _
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  cont := ContinuousMap.continuous_const'

def boundaryCoordinate (i : Fin n) : C(distinguishedBoundary c R, ℂ) :=
  ⟨fun z => z.val i, (continuous_apply i).comp continuous_subtype_val⟩

def poleMap (i : Fin n) (z : Fin n → ℂ) : C(distinguishedBoundary c R, ℂ) :=
  boundaryCoordinate c R i - constCLM c R (z i)

theorem poleMap_apply (i : Fin n) (z : Fin n → ℂ) (w : distinguishedBoundary c R) :
    poleMap c R i z w = w.val i - z i := rfl

theorem poleMap_ne_zero (i : Fin n) {z : Fin n → ℂ} (hz : z ∈ openPolydisc c R)
    (w : distinguishedBoundary c R) : poleMap c R i z w ≠ 0 :=
  sub_ne_zero.mpr (ne_of_mem_of_not_mem (w.property i) (ne_of_lt (hz i)))

def poleUnit (i : Fin n) {z : Fin n → ℂ} (hz : z ∈ openPolydisc c R) :
    C(distinguishedBoundary c R, ℂ)ˣ where
  val := poleMap c R i z
  inv := ⟨fun w => (poleMap c R i z w)⁻¹,
    (poleMap c R i z).continuous.inv₀ (poleMap_ne_zero c R i hz)⟩
  val_inv := by ext w; exact mul_inv_cancel₀ (poleMap_ne_zero c R i hz w)
  inv_val := by ext w; exact inv_mul_cancel₀ (poleMap_ne_zero c R i hz w)

def cauchyKernelMap (z : Fin n → ℂ) : C(distinguishedBoundary c R, ℂ) :=
  ∏ i : Fin n, Ring.inverse (poleMap c R i z)

theorem cauchyKernelMap_apply {z : Fin n → ℂ} (hz : z ∈ openPolydisc c R)
    (w : distinguishedBoundary c R) :
    cauchyKernelMap c R z w = ∏ i, (w.val i - z i)⁻¹ := by
  unfold cauchyKernelMap
  simp only [ContinuousMap.prod_apply]
  apply Finset.prod_congr rfl
  intro i _
  have he : poleMap c R i z = (poleUnit c R i hz : C(distinguishedBoundary c R, ℂ)) := rfl
  rw [he, Ring.inverse_unit]
  rfl

theorem analyticAt_cauchyKernelMap {z : Fin n → ℂ} (hz : z ∈ openPolydisc c R) :
    AnalyticAt ℂ (cauchyKernelMap c R) z := by
  apply Finset.analyticAt_prod
  intro i _
  have hp : AnalyticAt ℂ (poleMap c R i) z := by
    exact analyticAt_const.sub
      ((constCLM c R).analyticAt _ |>.comp ((ContinuousLinearMap.proj (R := ℂ) i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt z))
  have hi : AnalyticAt ℂ Ring.inverse (poleMap c R i z) :=
    analyticAt_inverse (𝕜 := ℂ) (poleUnit c R i hz)
  exact hi.comp hp

end Kernel

section CompactFamily

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def multiplyDataCLM (g : C(distinguishedBoundary c R, C(K, ℂ))) :
    C(distinguishedBoundary c R, ℂ) →L[ℂ] C(distinguishedBoundary c R, C(K, ℂ)) where
  toFun a := ⟨fun z => a z • g z, a.continuous.smul g.continuous⟩
  map_add' a b := by ext z t; simp [add_smul]
  map_smul' a b := by ext z t; simp [smul_smul]
  cont := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_eval.smul (g.continuous.comp continuous_snd)

theorem torusIntegral_family_apply
    {f : (Fin n → ℂ) → C(K, ℂ)} (hf : TorusIntegrable f c R) (t : K) :
    (torusIntegral f c R) t = torusIntegral (fun z => f z t) c R := by
  simpa only [torusIntegral, ContinuousMap.smul_apply] using
    ContinuousMap.integral_apply hf.function_integrable t

theorem torusIntegrable_cauchy_family {f : (Fin n → ℂ) → C(K, ℂ)}
    {z : Fin n → ℂ} (hR : ∀ i, 0 ≤ R i)
    (hf : ContinuousOn f (closedPolydisc c R)) (hz : z ∈ openPolydisc c R) :
    TorusIntegrable (fun w => (∏ i, (w i - z i)⁻¹) • f w) c R := by
  have hc := ((continuousOn_cauchyKernel hz).smul
    (hf.mono (boundary_subset_closed c R))).comp_continuous
      (continuous_torusMap c R) (torusMap_mem_boundary c hR)
  exact hc.continuousOn.integrableOn_compact isCompact_Icc

/-- Scalar holomorphy and compact-family continuity imply joint analyticity
of the actual Banach-valued family in every finite complex dimension. -/
theorem analyticAt_continuousFamily_polydisc
    {f : (Fin n → ℂ) → C(K, ℂ)} {z : Fin n → ℂ} (hR : ∀ i, 0 < R i)
    (hc : ContinuousOn f (closedPolydisc c R))
    (hd : ∀ t : K, ∀ w ∈ closedPolydisc c R, ∀ i : Fin n,
      DifferentiableAt ℂ (fun u => f (Function.update w i u) t) (w i))
    (hz : z ∈ openPolydisc c R) : AnalyticAt ℂ f z := by
  let data : C(distinguishedBoundary c R, C(K, ℂ)) :=
    ⟨fun w => f w, (hc.mono (boundary_subset_closed c R)).restrict⟩
  let L : C(distinguishedBoundary c R, ℂ) →L[ℂ] C(K, ℂ) :=
    (torusCLM c R (fun i => (hR i).le)).comp (multiplyDataCLM c R data)
  let κ : ℂ := 2 * Real.pi * I
  let A : (Fin n → ℂ) → C(K, ℂ) := fun q => (κ ^ n)⁻¹ • L (cauchyKernelMap c R q)
  have hκ : κ ≠ 0 := by
    dsimp only [κ]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hA : AnalyticAt ℂ A z :=
    ((L.analyticAt _).comp (analyticAt_cauchyKernelMap c R hz)).fun_const_smul
  apply hA.congr
  filter_upwards [(isOpen_openPolydisc c R).mem_nhds hz] with q hq
  have he : L (cauchyKernelMap c R q) =
      torusIntegral (fun w => (∏ i, (w i - q i)⁻¹) • f w) c R := by
    apply torusCLM_apply_of_eqOn c R (fun i => (hR i).le)
    intro w
    change cauchyKernelMap c R q w • f w = _
    rw [cauchyKernelMap_apply c R hq]
  ext t
  change ((κ ^ n)⁻¹ • L (cauchyKernelMap c R q)) t = f q t
  rw [ContinuousMap.smul_apply, he,
    torusIntegral_family_apply c R (torusIntegrable_cauchy_family c R (fun i => (hR i).le) hc hq)]
  have hct : ContinuousOn (fun w => f w t) (closedPolydisc c R) :=
    (ContinuousMap.evalCLM ℂ t).continuous.comp_continuousOn hc
  have hCauchy := torusIntegral_cauchy hR hct (hd t) hq
  simp only [ContinuousMap.smul_apply, smul_eq_mul] at *
  rw [hCauchy]
  change (κ ^ n)⁻¹ * (κ ^ n * f q t) = f q t
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hκ), one_mul]

omit [CompactSpace K] in
/-- Joint continuity on the compact product gives the continuous-function-space
form of continuity used above. -/
theorem continuousOn_family_of_joint {E : Type*} [TopologicalSpace E]
    {f : E → C(K, ℂ)} {S : Set E}
    (hc : ContinuousOn (fun p : E × K => f p.1 p.2) (S ×ˢ univ)) :
    ContinuousOn f S := by
  rw [continuousOn_iff_continuous_restrict]
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hc.comp_continuous (continuous_subtype_val.prodMap continuous_id)
    (fun p => ⟨p.1.property, mem_univ _⟩)

/-- General finite-dimensional compact-family theorem on an arbitrary open
complex parameter domain. The hypotheses concern only joint continuity and
ordinary scalar holomorphy of each fiber. -/
theorem analyticAt_continuousFamily_of_scalar
    {f : (Fin n → ℂ) → C(K, ℂ)} {Q : Set (Fin n → ℂ)} (hQ : IsOpen Q)
    (hc : ContinuousOn (fun p : (Fin n → ℂ) × K => f p.1 p.2) (Q ×ˢ univ))
    (hf : ∀ t : K, AnalyticOnNhd ℂ (fun q => f q t) Q)
    {z : Fin n → ℂ} (hz : z ∈ Q) : AnalyticAt ℂ f z := by
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds hz)
  let R : Fin n → ℝ := fun _ => ε / 2
  have hR : ∀ i, 0 < R i := fun _ => by dsimp only [R]; linarith
  have hsub : closedPolydisc z R ⊆ Q := by
    intro q hq
    apply hb
    apply lt_of_le_of_lt ((dist_pi_le_iff (show 0 ≤ ε / 2 by linarith)).mpr hq)
    linarith
  have hcf : ContinuousOn f (closedPolydisc z R) :=
    (continuousOn_family_of_joint hc).mono hsub
  have hdf : ∀ t : K, ∀ w ∈ closedPolydisc z R, ∀ i : Fin n,
      DifferentiableAt ℂ (fun u => f (Function.update w i u) t) (w i) := by
    intro t w hw i
    have hm : AnalyticAt ℂ (fun u : ℂ => Function.update w i u) (w i) := by
      apply AnalyticAt.pi
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [Function.update_self] using (analyticAt_id : AnalyticAt ℂ (fun u : ℂ => u) (w i))
      · simpa only [Function.update_of_ne hji] using
          (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => w j) (w i))
    have he : Function.update w i (w i) = w := Function.update_eq_self _ _
    exact ((hf t w (hsub hw)).comp_of_eq hm he).differentiableAt
  exact analyticAt_continuousFamily_polydisc z R hR hcf hdf
    (fun i => mem_ball_self (hR i))

/-- A common Banach-valued series controls all compact-family coefficients by
one actual geometric majorant. Its hypotheses are scalar holomorphy and joint
continuity; no common series or coefficient bound is assumed. -/
theorem exists_common_holomorphic_family_series
    {f : (Fin n → ℂ) → C(K, ℂ)} {Q : Set (Fin n → ℂ)} (hQ : IsOpen Q)
    (hc : ContinuousOn (fun p : (Fin n → ℂ) × K => f p.1 p.2) (Q ×ˢ univ))
    (hf : ∀ t : K, AnalyticOnNhd ℂ (fun q => f q t) Q)
    {z : Fin n → ℂ} (hz : z ∈ Q) :
    ∃ p : FormalMultilinearSeries ℂ (Fin n → ℂ) C(K, ℂ),
      ∃ R : ℝ≥0∞, ∃ C L : ℝ, 0 < R ∧ 0 < C ∧ 0 < L ∧
        HasFPowerSeriesOnBall f p z R ∧
        ∀ k : ℕ, ‖p k‖ ≤ C * L ^ k := by
  obtain ⟨p, R, hp⟩ := analyticAt_continuousFamily_of_scalar hQ hc hf hz
  obtain ⟨C, L, hC, hL, hb⟩ := p.le_mul_pow_of_radius_pos hp.radius_pos
  exact ⟨p, R, C, L, hp.r_pos, hC, hL, hp, hb⟩

section Weighted

variable [MeasurableSpace K] [BorelSpace K] {μ : Measure K} {ω : K → ℂ}

/-- Joint holomorphy of the actual weighted integral in any finite complex
dimension, with arbitrary integrable complex weights. -/
theorem analyticAt_weighted_holomorphicIntegral_of_joint
    {f : (Fin n → ℂ) → C(K, ℂ)} {Q : Set (Fin n → ℂ)} (hQ : IsOpen Q)
    (hc : ContinuousOn (fun p : (Fin n → ℂ) × K => f p.1 p.2) (Q ×ˢ univ))
    (hf : ∀ t : K, AnalyticOnNhd ℂ (fun q => f q t) Q)
    (hω : Integrable ω μ) {z : Fin n → ℂ} (hz : z ∈ Q) :
    AnalyticAt ℂ (fun q => ∫ t, ω t * f q t ∂μ) z :=
  ((HolomorphicCompactFamily.weightedIntegralCLM hω).analyticAt _).comp
    (analyticAt_continuousFamily_of_scalar hQ hc hf hz)

/-- Every ordered mixed derivative passes under the actual weighted complex
integral, with its integrability proved from compact-family holomorphy. -/
theorem all_derivatives_weighted_holomorphicIntegral_of_joint
    {f : (Fin n → ℂ) → C(K, ℂ)} {Q : Set (Fin n → ℂ)} (hQ : IsOpen Q)
    (hc : ContinuousOn (fun p : (Fin n → ℂ) × K => f p.1 p.2) (Q ×ˢ univ))
    (hf : ∀ t : K, AnalyticOnNhd ℂ (fun q => f q t) Q)
    (hω : Integrable ω μ) {z : Fin n → ℂ} (hz : z ∈ Q)
    (k : ℕ) (v : Fin k → (Fin n → ℂ)) :
    Integrable (fun t => ω t * iteratedFDeriv ℂ k (fun q => f q t) z v) μ ∧
    iteratedFDeriv ℂ k (fun q => ∫ t, ω t * f q t ∂μ) z v =
      ∫ t, ω t * iteratedFDeriv ℂ k (fun q => f q t) z v ∂μ := by
  have ha := analyticAt_continuousFamily_of_scalar hQ hc hf hz
  have ht (t : K) : iteratedFDeriv ℂ k (fun q => f q t) z v =
      iteratedFDeriv ℂ k f z v t := by
    have he := (ContinuousMap.evalCLM ℂ t).iteratedFDeriv_comp_left
      (ha.contDiffAt : ContDiffAt ℂ (k : WithTop ℕ∞) f z) (le_refl (k : WithTop ℕ∞))
    exact congrArg (fun p : (Fin n → ℂ)[×k]→L[ℂ] ℂ => p v) he
  have hi := (HolomorphicCompactFamily.weightedIntegralCLM hω).iteratedFDeriv_comp_left
    (ha.contDiffAt : ContDiffAt ℂ (k : WithTop ℕ∞) f z) (le_refl (k : WithTop ℕ∞))
  constructor
  · simpa only [ht] using
      HolomorphicCompactFamily.integrable_weightedContinuousMap hω (iteratedFDeriv ℂ k f z v)
  · simpa only [ht] using congrArg (fun p : (Fin n → ℂ)[×k]→L[ℂ] ℂ => p v) hi

end Weighted

end CompactFamily

end LeanVerification.PolydiscCauchy
