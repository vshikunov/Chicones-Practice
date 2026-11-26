import LeanVerification.Loud.CompactAnalyticIntegral

noncomputable section

open Set Filter Metric
open scoped Topology ENNReal NNReal

namespace LeanVerification.AnalyticEvenDescent

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Space (E : Type*) := E × ℝ

def parameterPart : Space E →L[ℝ] Space E :=
  (ContinuousLinearMap.fst ℝ E ℝ).prod 0

def amplitudeUnit : Space E := (0, 1)

theorem parameterPart_apply (y : Space E) : parameterPart y = (y.1, 0) := rfl

theorem norm_parameterPart_apply_le (y : Space E) : ‖parameterPart y‖ ≤ ‖y‖ := by
  simp only [parameterPart_apply, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  exact le_max_left _ _

omit [NormedSpace ℝ E] in
theorem norm_amplitudeUnit : ‖amplitudeUnit (E := E)‖ = 1 := by
  simp [amplitudeUnit, Prod.norm_def]

def amplitudeMonomial (j : ℕ) : (Space E)[×j]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin j) ℝ).compContinuousLinearMap
    (fun _ => ContinuousLinearMap.snd ℝ E ℝ)

theorem amplitudeMonomial_apply (j : ℕ) (y : Space E) :
    amplitudeMonomial j (fun _ => y) = y.2 ^ j := by
  simp [amplitudeMonomial, ContinuousMultilinearMap.mkPiAlgebra_apply]

theorem norm_amplitudeMonomial_le (j : ℕ) :
    ‖amplitudeMonomial (E := E) j‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro v
  change ‖∏ i, (v i).2‖ ≤ 1 * ∏ i, ‖v i‖
  rw [norm_prod, one_mul]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => norm_snd_le (v i))

def parameterCoefficient (p : FormalMultilinearSeries ℝ (Space E) ℝ)
    (k l : ℕ) : (Space E)[×l]→L[ℝ] ℝ :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Space E) ℝ
      (fun _ => amplitudeUnit)).compContinuousMultilinearMap
        (p.changeOriginSeries k l)).compContinuousLinearMap (fun _ => parameterPart)

theorem parameterCoefficient_apply (p : FormalMultilinearSeries ℝ (Space E) ℝ)
    (k l : ℕ) (v : Fin l → Space E) :
    parameterCoefficient p k l v =
      p.changeOriginSeries k l (fun i => parameterPart (v i)) (fun _ => amplitudeUnit) := rfl

theorem norm_parameterCoefficient_le (p : FormalMultilinearSeries ℝ (Space E) ℝ)
    (k l : ℕ) : ‖parameterCoefficient p k l‖ ≤ ‖p.changeOriginSeries k l‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    (norm_nonneg (p.changeOriginSeries k l))
  intro v
  rw [parameterCoefficient_apply]
  calc
    _ ≤ ‖p.changeOriginSeries k l (fun i => parameterPart (v i))‖ *
        ∏ _ : Fin k, ‖amplitudeUnit (E := E)‖ :=
      (p.changeOriginSeries k l (fun i => parameterPart (v i))).le_opNorm _
    _ = ‖p.changeOriginSeries k l (fun i => parameterPart (v i))‖ := by
      simp only [norm_amplitudeUnit, Finset.prod_const_one, mul_one]
    _ ≤ ‖p.changeOriginSeries k l‖ * ∏ i, ‖parameterPart (v i)‖ :=
      (p.changeOriginSeries k l).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun i _ => norm_parameterPart_apply_le (v i)))
      (norm_nonneg (p.changeOriginSeries k l))

def energyTerm (p : FormalMultilinearSeries ℝ (Space E) ℝ)
    (j l : ℕ) : (Space E)[×(l + j)]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ (Space E) ℝ finSumFinEquiv)
    ((ContinuousMultilinearMap.currySumEquiv ℝ (Fin l) (Fin j) (Space E) ℝ).symm
      ((parameterCoefficient p (2 * j) l).smulRight (amplitudeMonomial j)))

theorem energyTerm_apply (p : FormalMultilinearSeries ℝ (Space E) ℝ)
    (j l : ℕ) (y : Space E) :
    energyTerm p j l (fun _ => y) =
      parameterCoefficient p (2 * j) l (fun _ => y) * y.2 ^ j := by
  change ((parameterCoefficient p (2 * j) l).smulRight (amplitudeMonomial j))
    (fun _ => y) (fun _ => y) = _
  simp only [ContinuousMultilinearMap.smulRight_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul, amplitudeMonomial_apply]

theorem norm_energyTerm_le (p : FormalMultilinearSeries ℝ (Space E) ℝ)
    (j l : ℕ) : ‖energyTerm p j l‖ ≤ ‖p.changeOriginSeries (2 * j) l‖ := by
  simp only [energyTerm, LinearIsometryEquiv.norm_map, ContinuousMultilinearMap.norm_smulRight]
  exact (mul_le_of_le_one_right (norm_nonneg _) (norm_amplitudeMonomial_le j)).trans
    (norm_parameterCoefficient_le p (2 * j) l)

theorem norm_changeOriginSeries_le_two_pow
    (p : FormalMultilinearSeries ℝ (Space E) ℝ) (k l : ℕ) :
    ‖p.changeOriginSeries k l‖ ≤ (2 : ℝ) ^ (k + l) * ‖p (k + l)‖ := by
  classical
  have hc : Fintype.card {s : Finset (Fin (k + l)) // s.card = l} ≤ 2 ^ (k + l) := by
    calc
      _ ≤ Fintype.card (Finset (Fin (k + l))) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = _ := by simp
  calc
    _ ≤ ∑ s : {s : Finset (Fin (k + l)) // s.card = l},
        ‖p.changeOriginSeriesTerm k l s s.property‖ := by
      change ‖∑ s : {s : Finset (Fin (k + l)) // s.card = l},
        p.changeOriginSeriesTerm k l s s.property‖ ≤ _
      exact norm_sum_le Finset.univ
        (fun s : {s : Finset (Fin (k + l)) // s.card = l} =>
          p.changeOriginSeriesTerm k l s s.property)
    _ = (Fintype.card {s : Finset (Fin (k + l)) // s.card = l} : ℝ) *
        ‖p (k + l)‖ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (norm_nonneg _)

theorem exists_energyTerm_geometric_bound
    {p : FormalMultilinearSeries ℝ (Space E) ℝ} (hp : 0 < p.radius) :
    ∃ C M : ℝ, 0 < C ∧ 1 ≤ M ∧ ∀ j l,
      ‖energyTerm p j l‖ ≤ C * M ^ (j + l) := by
  obtain ⟨C, r, hC, hr, hpr⟩ := p.le_mul_pow_of_radius_pos hp
  let R := max 1 (2 * r)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR : 0 ≤ R := zero_le_one.trans hR1
  refine ⟨C, R ^ 2, hC, one_le_pow₀ hR1, ?_⟩
  intro j l
  calc
    ‖energyTerm p j l‖ ≤ ‖p.changeOriginSeries (2 * j) l‖ := norm_energyTerm_le p j l
    _ ≤ (2 : ℝ) ^ (2 * j + l) * ‖p (2 * j + l)‖ :=
      norm_changeOriginSeries_le_two_pow p (2 * j) l
    _ ≤ (2 : ℝ) ^ (2 * j + l) * (C * r ^ (2 * j + l)) :=
      mul_le_mul_of_nonneg_left (hpr _) (by positivity)
    _ = C * (2 * r) ^ (2 * j + l) := by rw [mul_pow]; ring
    _ ≤ C * R ^ (2 * j + l) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _) hC.le
    _ ≤ C * R ^ (2 * (j + l)) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1 (by omega)) hC.le
    _ = C * (R ^ 2) ^ (j + l) := by rw [pow_mul]

def energySeries (p : FormalMultilinearSeries ℝ (Space E) ℝ) :
    FormalMultilinearSeries ℝ (Space E) ℝ := fun n =>
  ∑ s : ↥(Finset.antidiagonal n),
    (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ (Space E) ℝ
      (finCongr (Finset.mem_antidiagonal.mp s.property)))
        (energyTerm p s.val.2 s.val.1)

theorem energySeries_apply (p : FormalMultilinearSeries ℝ (Space E) ℝ)
    (n : ℕ) (y : Space E) :
    energySeries p n (fun _ => y) =
      ∑ s : ↥(Finset.antidiagonal n),
        energyTerm p s.val.2 s.val.1 (fun _ => y) := by
  simp only [energySeries, ContinuousMultilinearMap.sum_apply]
  rfl

theorem norm_energySeries_le {p : FormalMultilinearSeries ℝ (Space E) ℝ}
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ j l, ‖energyTerm p j l‖ ≤ C * M ^ (j + l)) (n : ℕ) :
    ‖energySeries p n‖ ≤ C * (2 * M) ^ n := by
  classical
  have hn : (n + 1 : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast Nat.succ_le_of_lt (show n < 2 ^ n from Nat.lt_two_pow_self)
  calc
    _ ≤ ∑ s : ↥(Finset.antidiagonal n), ‖energyTerm p s.val.2 s.val.1‖ := by
      unfold energySeries
      exact (norm_sum_le _ _).trans_eq (by simp)
    _ ≤ ∑ _s : ↥(Finset.antidiagonal n), C * M ^ n := by
      apply Finset.sum_le_sum
      intro s _
      have he : s.val.2 + s.val.1 = n := by
        have := Finset.mem_antidiagonal.mp s.property
        omega
      simpa only [he] using hb s.val.2 s.val.1
    _ = (n + 1 : ℝ) * (C * M ^ n) := by simp
    _ ≤ (2 : ℝ) ^ n * (C * M ^ n) :=
      mul_le_mul_of_nonneg_right hn (mul_nonneg hC (pow_nonneg hM _))
    _ = C * (2 * M) ^ n := by rw [mul_pow]; ring

theorem energySeries_radius_pos {p : FormalMultilinearSeries ℝ (Space E) ℝ}
    (hp : 0 < p.radius) : 0 < (energySeries p).radius := by
  obtain ⟨C, M, hC, hM, hb⟩ := exists_energyTerm_geometric_bound hp
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let r : ℝ≥0 := ⟨(2 * M)⁻¹, inv_nonneg.mpr (by positivity)⟩
  have hr : 0 < r := inv_pos.mpr (by positivity : 0 < 2 * M)
  have hle : (r : ℝ≥0∞) ≤ (energySeries p).radius := by
    apply FormalMultilinearSeries.le_radius_of_bound _ C
    intro n
    calc
      ‖energySeries p n‖ * (r : ℝ) ^ n ≤ (C * (2 * M) ^ n) * (r : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (norm_energySeries_le hC.le hMpos.le hb n)
          (pow_nonneg r.coe_nonneg _)
      _ = C := by
        dsimp only [r, NNReal.coe_mk]
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (by positivity : 2 * M ≠ 0),
          one_pow, mul_one]
  exact (ENNReal.coe_pos.mpr hr).trans_le hle

theorem summable_energyTerm {p : FormalMultilinearSeries ℝ (Space E) ℝ}
    {C M : ℝ} (_hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ j l, ‖energyTerm p j l‖ ≤ C * M ^ (j + l))
    {y : Space E} (hy : M * ‖y‖ < 1) :
    Summable (fun jl : ℕ × ℕ => energyTerm p jl.1 jl.2 (fun _ => y)) := by
  have ha : 0 ≤ M * ‖y‖ := mul_nonneg hM (norm_nonneg _)
  have hg : Summable (fun n : ℕ => (M * ‖y‖) ^ n) :=
    summable_geometric_of_abs_lt_one (by simpa only [abs_of_nonneg ha] using hy)
  have hgg := (hg.mul_of_nonneg hg (fun n => pow_nonneg ha n)
    (fun n => pow_nonneg ha n)).mul_left C
  apply Summable.of_norm_bounded _ hgg
  intro jl
  calc
    ‖energyTerm p jl.1 jl.2 (fun _ => y)‖ ≤
        ‖energyTerm p jl.1 jl.2‖ * ‖y‖ ^ (jl.2 + jl.1) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (energyTerm p jl.1 jl.2).le_opNorm (fun _ => y)
    _ ≤ (C * M ^ (jl.1 + jl.2)) * ‖y‖ ^ (jl.2 + jl.1) :=
      mul_le_mul_of_nonneg_right (hb _ _) (pow_nonneg (norm_nonneg _) _)
    _ = C * ((M * ‖y‖) ^ jl.1 * (M * ‖y‖) ^ jl.2) := by
      simp only [mul_pow, pow_add]
      ring

theorem energySeries_sum_eq_tsum
    {p : FormalMultilinearSeries ℝ (Space E) ℝ} {y : Space E}
    (hs : Summable (fun jl : ℕ × ℕ => energyTerm p jl.1 jl.2 (fun _ => y))) :
    (energySeries p).sum y = ∑' j, ∑' l, energyTerm p j l (fun _ => y) := by
  classical
  have hswap : Summable (fun lj : ℕ × ℕ => energyTerm p lj.2 lj.1 (fun _ => y)) :=
    hs.comp_injective (i := Prod.swap) Prod.swap_injective
  have hsig : Summable (fun s : Σ n : ℕ, ↥(Finset.antidiagonal n) =>
      energyTerm p s.2.val.2 s.2.val.1 (fun _ => y)) :=
    Finset.sigmaAntidiagonalEquivProd.summable_iff.mpr hswap
  calc
    _ = ∑' n, ∑' s : ↥(Finset.antidiagonal n),
        energyTerm p s.val.2 s.val.1 (fun _ => y) := by
      simp only [FormalMultilinearSeries.sum, energySeries_apply, tsum_fintype]
    _ = ∑' s : Σ n : ℕ, ↥(Finset.antidiagonal n),
        energyTerm p s.2.val.2 s.2.val.1 (fun _ => y) :=
      (hsig.tsum_sigma' (fun n => (hasSum_fintype _).summable)).symm
    _ = ∑' lj : ℕ × ℕ, energyTerm p lj.2 lj.1 (fun _ => y) :=
      Finset.sigmaAntidiagonalEquivProd.tsum_eq
        (fun lj : ℕ × ℕ => energyTerm p lj.2 lj.1 (fun _ => y))
    _ = ∑' jl : ℕ × ℕ, energyTerm p jl.1 jl.2 (fun _ => y) :=
      (Equiv.prodComm ℕ ℕ).tsum_eq
        (fun jl : ℕ × ℕ => energyTerm p jl.1 jl.2 (fun _ => y))
    _ = _ := hs.tsum_prod

theorem hasSum_parameterCoefficient
    (p : FormalMultilinearSeries ℝ (Space E) ℝ) (k : ℕ) {y : Space E}
    (hy : (‖parameterPart y‖₊ : ℝ≥0∞) < p.radius) :
    HasSum (fun l => parameterCoefficient p k l (fun _ => y))
      (p.changeOrigin (parameterPart y) k (fun _ => amplitudeUnit)) := by
  have hsum := (p.hasFPowerSeriesOnBall_changeOrigin k
    ((bot_le : (0 : ℝ≥0∞) ≤ ‖parameterPart y‖₊).trans_lt hy)).hasSum
      (mem_emetric_ball_zero_iff.mpr hy)
  simpa only [parameterCoefficient_apply, zero_add] using
    ContinuousMultilinearMap.hasSum_eval hsum (fun _ => amplitudeUnit)

theorem energySeries_sum_eq_even_series
    {p : FormalMultilinearSeries ℝ (Space E) ℝ} {y : Space E}
    (hy : (‖parameterPart y‖₊ : ℝ≥0∞) < p.radius)
    (hs : Summable (fun jl : ℕ × ℕ => energyTerm p jl.1 jl.2 (fun _ => y))) :
    (energySeries p).sum y =
      ∑' j, p.changeOrigin (parameterPart y) (2 * j)
        (fun _ => amplitudeUnit) * y.2 ^ j := by
  rw [energySeries_sum_eq_tsum hs]
  congr 1
  funext j
  simp_rw [energyTerm_apply]
  exact ((hasSum_parameterCoefficient p (2 * j) hy).mul_right (y.2 ^ j)).tsum_eq

theorem hasSum_energySeries_even
    {p : FormalMultilinearSeries ℝ (Space E) ℝ} {y : Space E}
    (hy : (‖parameterPart y‖₊ : ℝ≥0∞) < p.radius)
    (hs : Summable (fun jl : ℕ × ℕ => energyTerm p jl.1 jl.2 (fun _ => y))) :
    HasSum (fun j => p.changeOrigin (parameterPart y) (2 * j)
        (fun _ => amplitudeUnit) * y.2 ^ j) ((energySeries p).sum y) := by
  have hinner (j : ℕ) : (∑' l, energyTerm p j l (fun _ => y)) =
      p.changeOrigin (parameterPart y) (2 * j) (fun _ => amplitudeUnit) * y.2 ^ j := by
    simp_rw [energyTerm_apply]
    exact ((hasSum_parameterCoefficient p (2 * j) hy).mul_right (y.2 ^ j)).tsum_eq
  have houter : Summable (fun j => p.changeOrigin (parameterPart y) (2 * j)
      (fun _ => amplitudeUnit) * y.2 ^ j) := by
    simpa only [hinner] using hs.prod
  rw [energySeries_sum_eq_even_series hy hs]
  exact houter.hasSum

theorem multilinear_amplitude_eval (k : ℕ) (p : (Space E)[×k]→L[ℝ] ℝ) (r : ℝ) :
    p (fun _ => ((0 : E), r)) = p (fun _ => amplitudeUnit) * r ^ k := by
  have he : (fun _ : Fin k => ((0 : E), r)) =
      (fun _ : Fin k => r • amplitudeUnit) := by
    funext i
    simp [amplitudeUnit]
  rw [he, ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

theorem hasSum_amplitude_slice
    {f : Space E → ℝ} {p : FormalMultilinearSeries ℝ (Space E) ℝ}
    {x₀ d : E} {r : ℝ} {R : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p (x₀, 0) R)
    (hsmall : (‖(d, (0 : ℝ))‖₊ : ℝ≥0∞) + ‖((0 : E), r)‖₊ < R) :
    HasSum (fun k => p.changeOrigin (d, 0) k (fun _ => amplitudeUnit) * r ^ k)
      (f (x₀ + d, r)) := by
  have hd : (‖(d, (0 : ℝ))‖₊ : ℝ≥0∞) < R :=
    (le_add_right le_rfl).trans_lt hsmall
  have hr : ((0 : E), r) ∈ EMetric.ball 0 (R - ‖(d, (0 : ℝ))‖₊) := by
    rw [mem_emetric_ball_zero_iff, lt_tsub_iff_right]
    simpa only [enorm_eq_nnnorm, add_comm] using hsmall
  have hs := (hp.changeOrigin hd).hasSum hr
  simpa only [multilinear_amplitude_eval, Prod.mk_add_mk, add_zero, zero_add] using hs

/-- The regrouped real series descends the even part of the amplitude series.
The summability premise here is discharged on a neighborhood in the following theorem. -/
theorem energySeries_sum_eq_even_part
    {f : Space E → ℝ} {p : FormalMultilinearSeries ℝ (Space E) ℝ}
    {x₀ d : E} {r : ℝ} {R : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p (x₀, 0) R)
    (hsmall : (‖(d, (0 : ℝ))‖₊ : ℝ≥0∞) + ‖((0 : E), r)‖₊ < R)
    (hs : Summable (fun jl : ℕ × ℕ =>
      energyTerm p jl.1 jl.2 (fun _ => (d, r ^ 2)))) :
    (energySeries p).sum (d, r ^ 2) = (f (x₀ + d, r) + f (x₀ + d, -r)) / 2 := by
  have hd : (‖(d, (0 : ℝ))‖₊ : ℝ≥0∞) < p.radius :=
    ((le_add_right le_rfl).trans_lt hsmall).trans_le hp.r_le
  have hq := hasSum_energySeries_even (y := (d, r ^ 2)) hd hs
  have hpos := hasSum_amplitude_slice hp hsmall
  have hneg := hasSum_amplitude_slice (r := -r) hp
    (by simpa only [Prod.nnnorm_def, nnnorm_neg] using hsmall)
  let c (n : ℕ) := p.changeOrigin (d, 0) n (fun _ => amplitudeUnit)
  let b (n : ℕ) := (c n * r ^ n + c n * (-r) ^ n) / 2
  have hb : HasSum b ((f (x₀ + d, r) + f (x₀ + d, -r)) / 2) :=
    (hpos.add hneg).div_const 2
  have heven : HasSum (fun j => b (2 * j)) ((energySeries p).sum (d, r ^ 2)) := by
    convert hq using 1
    funext j
    dsimp only [b, c, parameterPart_apply]
    rw [pow_mul, pow_mul, neg_sq]
    ring
  have hodd : HasSum (fun j => b (2 * j + 1)) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) using 1
    funext j
    dsimp only [b]
    simp only [pow_succ, pow_mul, neg_sq]
    ring
  have hfull := HasSum.even_add_odd (f := b) heven hodd
  simpa only [add_zero] using hfull.unique hb

/-- Joint real-analytic descent of the even part under squaring the final coordinate.
The resulting analytic function is defined for both signs of its final argument. -/
theorem exists_analytic_evenPart_descent
    {f : Space E → ℝ} {x₀ : E} (hf : AnalyticAt ℝ f (x₀, 0)) :
    ∃ G : Space E → ℝ, AnalyticAt ℝ G (x₀, 0) ∧
      ∀ᶠ z in 𝓝 (x₀, (0 : ℝ)),
        G (z.1, z.2 ^ 2) = (f z + f (z.1, -z.2)) / 2 := by
  obtain ⟨p, R, hp⟩ := hf
  let G : Space E → ℝ := fun z => (energySeries p).sum (z.1 - x₀, z.2)
  have hG : AnalyticAt ℝ G (x₀, 0) := by
    have hmap : AnalyticAt ℝ (fun z : Space E => (z.1 - x₀, z.2)) (x₀, 0) :=
      (analyticAt_fst.sub analyticAt_const).prod analyticAt_snd
    exact ((energySeries p).hasFPowerSeriesOnBall
      (energySeries_radius_pos hp.radius_pos)).analyticAt.comp_of_eq hmap (by simp)
  obtain ⟨C, M, hC, hM, hb⟩ := exists_energyTerm_geometric_bound hp.radius_pos
  have hsmall : ∀ᶠ z : Space E in 𝓝 (x₀, 0),
      (‖(z.1 - x₀, (0 : ℝ))‖₊ : ℝ≥0∞) + ‖((0 : E), z.2)‖₊ < R := by
    have hc : Continuous (fun z : Space E =>
        ‖(z.1 - x₀, (0 : ℝ))‖ₑ + ‖((0 : E), z.2)‖ₑ) := by fun_prop
    apply (isOpen_lt hc continuous_const).mem_nhds
    simpa using hp.r_pos
  have hbound : ∀ᶠ z : Space E in 𝓝 (x₀, 0),
      M * ‖(z.1 - x₀, z.2 ^ 2)‖ < 1 := by
    apply (isOpen_lt (show Continuous (fun z : Space E =>
      M * ‖(z.1 - x₀, z.2 ^ 2)‖) by fun_prop) continuous_const).mem_nhds
    simp
  refine ⟨G, hG, ?_⟩
  filter_upwards [hsmall, hbound] with z hzs hzb
  have he := energySeries_sum_eq_even_part hp hzs
    (summable_energyTerm hC.le (zero_le_one.trans hM) hb hzb)
  have hx : x₀ + (z.1 - x₀) = z.1 := by abel
  simpa only [G, hx, Prod.mk.eta] using he

/-- A locally even, jointly analytic amplitude function has a jointly analytic
signed-energy descent. No analyticity hypothesis is imposed on the descent. -/
theorem exists_analytic_even_descent
    {f : Space E → ℝ} {x₀ : E} (hf : AnalyticAt ℝ f (x₀, 0))
    (heven : ∀ᶠ z in 𝓝 (x₀, (0 : ℝ)), f (z.1, -z.2) = f z) :
    ∃ G : Space E → ℝ, AnalyticAt ℝ G (x₀, 0) ∧
      ∀ᶠ z in 𝓝 (x₀, (0 : ℝ)), G (z.1, z.2 ^ 2) = f z := by
  obtain ⟨G, hG, he⟩ := exists_analytic_evenPart_descent hf
  refine ⟨G, hG, ?_⟩
  filter_upwards [he, heven] with z hz hze
  rw [hz, hze]
  ring

end LeanVerification.AnalyticEvenDescent
