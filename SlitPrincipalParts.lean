import LeanVerification.SlitPhysicalRepresentation
import LeanVerification.SpectralAtoms

/-! Actual finite principal parts: their holomorphy, bank limits and residues.
The pole coefficients are real and their signs are retained. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace LeanVerification.SlitContour

def polePart {N : ℕ} (t A : Fin N → ℝ) (z : ℂ) : ℂ :=
  ∑ j, (A j : ℂ) / ((t j : ℂ)-z)

theorem analyticAt_polePart {N : ℕ} (t A : Fin N → ℝ) {z : ℂ}
    (hz : ∀ j, z ≠ (t j : ℂ)) : AnalyticAt ℂ (polePart t A) z := by
  apply Finset.analyticAt_sum
  intro j hj
  exact analyticAt_const.div (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr (hz j).symm)

theorem continuousAt_polePart {N : ℕ} (t A : Fin N → ℝ) {z : ℂ}
    (hz : ∀ j, z ≠ (t j : ℂ)) : ContinuousAt (polePart t A) z :=
  (analyticAt_polePart t A hz).continuousAt

theorem differentiableOn_polePart {N : ℕ} (t A : Fin N → ℝ) {H : ℝ}
    (ht : ∀ j, H ≤ t j) : DifferentiableOn ℂ (polePart t A) (domain H) := by
  intro z hz
  apply (analyticAt_polePart t A ?_).differentiableAt.differentiableWithinAt
  intro j he
  rw [he] at hz
  have hh : t j < H := by simpa [domain] using hz
  exact (not_lt.mpr (ht j)) hh

theorem polePart_ofReal {N : ℕ} (t A : Fin N → ℝ) (x : ℝ) :
    polePart t A (x : ℂ) = ((∑ j, A j/(t j-x) : ℝ) : ℂ) := by
  simp only [polePart,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_sub]

theorem polePart_real {N : ℕ} (t A : Fin N → ℝ) (x : ℝ) :
    (polePart t A (x : ℂ)).im=0 := by rw [polePart_ofReal]; exact Complex.ofReal_im _

theorem polePart_bank_limit {N : ℕ} (t A : Fin N → ℝ) {x : ℝ}
    (hx : x ∉ Set.range t) (s : Set ℂ) :
    Tendsto (polePart t A) (𝓝[s] (x : ℂ)) (𝓝 (polePart t A (x : ℂ))) := by
  apply (continuousAt_polePart t A ?_).tendsto.mono_left nhdsWithin_le_nhds
  intro j he
  apply hx
  exact ⟨j,(Complex.ofReal_inj.mp he).symm⟩

theorem add_polePart_bank_limit {N : ℕ} (t A : Fin N → ℝ) {f : ℂ → ℂ}
    {x : ℝ} {u : ℂ} {s : Set ℂ} (hx : x ∉ Set.range t)
    (hf : Tendsto f (𝓝[s] (x : ℂ)) (𝓝 u)) :
    Tendsto (fun z => f z+polePart t A z) (𝓝[s] (x : ℂ))
      (𝓝 (u+polePart t A (x : ℂ))) :=
  hf.add (polePart_bank_limit t A hx s)

theorem add_polePart_bank_im {N : ℕ} (t A : Fin N → ℝ) (x : ℝ) (u : ℂ) :
    (u+polePart t A (x : ℂ)).im=u.im := by
  rw [Complex.add_im,polePart_real,add_zero]

theorem add_polePart_density {N : ℕ} (t A : Fin N → ℝ) (x : ℝ) (u : ℂ) :
    Real.sqrt x*(u+polePart t A (x : ℂ)).im=Real.sqrt x*u.im := by
  rw [add_polePart_bank_im]

/-- The finite sum has the signed residue -A_j at each distinct pole. -/
theorem polePart_residue {N : ℕ} {t : Fin N → ℝ} (ht : Function.Injective t)
    (A : Fin N → ℝ) (j : Fin N) :
    Tendsto (fun z : ℂ => (z-(t j : ℂ))*polePart t A z)
      (𝓝[≠] (t j : ℂ)) (𝓝 (-(A j : ℂ))) := by
  classical
  let rest : ℂ → ℂ := fun z => ∑ k ∈ Finset.univ.erase j,
    (A k : ℂ)/((t k : ℂ)-z)
  have hra : AnalyticAt ℂ rest (t j : ℂ) := by
    apply Finset.analyticAt_sum
    intro k hk
    apply analyticAt_const.div (analyticAt_const.sub analyticAt_id)
    apply sub_ne_zero.mpr
    intro he
    have hkj : k=j := ht (Complex.ofReal_inj.mp he)
    exact (Finset.ne_of_mem_erase hk) hkj
  have hr := hra.continuousAt
  have hzero : Tendsto (fun z : ℂ => (z-(t j : ℂ))*rest z)
      (𝓝[≠] (t j : ℂ)) (𝓝 0) := by
    simpa only [id_eq,sub_self,zero_mul] using
      ((continuousAt_id.sub_const (t j : ℂ)).mul hr).mono_left nhdsWithin_le_nhds
  have he : ∀ z : ℂ, polePart t A z=(A j : ℂ)/((t j : ℂ)-z)+rest z := by
    intro z
    exact (Finset.add_sum_erase Finset.univ (fun k => (A k : ℂ)/((t k : ℂ)-z))
      (Finset.mem_univ j)).symm
  have hs := (SpectralAtoms.simple_pole_residue (A j : ℂ) (t j : ℂ)).add hzero
  simpa only [he,mul_add,add_zero] using hs

/-- A strictly sublinear algebraic boundary singularity has zero residue
coefficient along the actual slit domain. -/
theorem boundary_growth_residue_zero {f : ℂ → ℂ} {s : Set ℂ} {p : ℂ}
    {r M β : ℝ} (hp : p ∉ s) (hr : 0 < r) (hβ : β < 1)
    (hf : ∀ z ∈ s, dist z p < r → ‖f z‖ ≤ M*dist z p^(-β)) :
    Tendsto (fun z => (z-p)*f z) (𝓝[s] p) (𝓝 0) := by
  have hd : Tendsto (fun z : ℂ => dist z p) (𝓝[s] p) (𝓝 0) := by
    have hc : ContinuousAt (fun z : ℂ => dist z p) p := by fun_prop
    simpa only [dist_self] using hc.tendsto.mono_left (show 𝓝[s] p ≤ 𝓝 p from nhdsWithin_le_nhds)
  have he : 0 < 1-β := sub_pos.mpr hβ
  have hm : Tendsto (fun z : ℂ => M*dist z p^(1-β)) (𝓝[s] p) (𝓝 0) := by
    simpa only [Real.zero_rpow he.ne',mul_zero] using
      (tendsto_const_nhds.mul (hd.rpow_const (Or.inr he.le)))
  apply squeeze_zero_norm' ?_ hm
  filter_upwards [self_mem_nhdsWithin,hd.eventually (Iio_mem_nhds hr)] with z hz hzr
  have hzp : z ≠ p := by intro h; exact hp (h ▸ hz)
  have hpos : 0 < dist z p := dist_pos.mpr hzp
  rw [norm_mul,←dist_eq_norm_sub]
  calc
    dist z p*‖f z‖ ≤ dist z p*(M*dist z p^(-β)) :=
      mul_le_mul_of_nonneg_left (hf z hz hzr) hpos.le
    _ = M*dist z p^(1-β) := by
      rw [sub_eq_add_neg,Real.rpow_add hpos,Real.rpow_one]
      ring

theorem PhysicalCutData.residue_coefficient_zero {f : ℂ → ℂ} {H : ℝ}
    (d : PhysicalCutData f H) (j : Fin d.count) :
    Tendsto (fun z => (z-(d.cutpoint j : ℂ))*f z)
      (𝓝[domain H] (d.cutpoint j : ℂ)) (𝓝 0) := by
  obtain ⟨r,hr,M,_,hf⟩ := d.local_growth j
  apply boundary_growth_residue_zero ?_ hr (d.exponent_lt_one j) hf
  simpa only [domain,mem_setOf_eq,Complex.ofReal_re,Complex.ofReal_im,ne_eq,
    not_true_eq_false,or_false,not_lt] using d.cutpoint_ge j

theorem PhysicalCutData.full_pole_residue {f : ℂ → ℂ} {H : ℝ}
    (d : PhysicalCutData f H) {N : ℕ} {t : Fin N → ℝ}
    (ht : Function.Injective t) (A : Fin N → ℝ)
    (j : Fin N) (k : Fin d.count) (hjk : t j=d.cutpoint k) :
    Tendsto (fun z => (z-(t j : ℂ))*(f z+polePart t A z))
      (𝓝[domain H] (t j : ℂ)) (𝓝 (-(A j : ℂ))) := by
  have hzero : Tendsto (fun z => (z-(t j : ℂ))*f z)
      (𝓝[domain H] (t j : ℂ)) (𝓝 0) := by
    simpa only [hjk] using d.residue_coefficient_zero k
  have hsub : 𝓝[domain H] (t j : ℂ) ≤ 𝓝[≠] (t j : ℂ) := by
    apply nhdsWithin_mono
    intro z hz
    change z ≠ (t j : ℂ)
    intro he
    rw [he] at hz
    have hlt : t j < H := by simpa [domain] using hz
    exact (not_lt.mpr (hjk ▸ d.cutpoint_ge k)) hlt
  simpa only [mul_add,zero_add] using hzero.add ((polePart_residue ht A j).mono_left hsub)

end LeanVerification.SlitContour
