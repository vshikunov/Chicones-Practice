import LeanVerification.Loud.CubicWidth

/-!
Every fixed mixed parameter derivative and every fixed Euler derivative
of a jointly analytic cubic input retains its cubic factor uniformly on
compact subsets. The differential operators use actual Frechet derivatives.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace LeanVerification.CubicDerivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def directional (v : E × ℝ) (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  fderiv ℝ f p v

def euler (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  p.2 * directional (0, 1) f p

def liftedEuler (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ := 3 * f p + euler f p

def cubicProduct (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ := p.2 ^ 3 * f p

def parameterDerivatives : List E → (E × ℝ → ℝ) → (E × ℝ → ℝ)
  | [], f => f
  | v :: vs, f => directional (v, 0) (parameterDerivatives vs f)

theorem analyticAt_directional {f : E × ℝ → ℝ} {p : E × ℝ}
    (hf : AnalyticAt ℝ f p) (v : E × ℝ) : AnalyticAt ℝ (directional v f) p := by
  exact ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp hf.fderiv

theorem analyticAt_euler {f : E × ℝ → ℝ} {p : E × ℝ}
    (hf : AnalyticAt ℝ f p) : AnalyticAt ℝ (euler f) p :=
  analyticAt_snd.mul (analyticAt_directional hf (0, 1))

theorem analyticAt_liftedEuler {f : E × ℝ → ℝ} {p : E × ℝ}
    (hf : AnalyticAt ℝ f p) : AnalyticAt ℝ (liftedEuler f) p :=
  (analyticAt_const.mul hf).add (analyticAt_euler hf)

theorem analyticAt_cubicProduct {f : E × ℝ → ℝ} {p : E × ℝ}
    (hf : AnalyticAt ℝ f p) : AnalyticAt ℝ (cubicProduct f) p :=
  (analyticAt_snd.pow 3).mul hf

theorem directional_cubicProduct {f : E × ℝ → ℝ} {p v : E × ℝ}
    (hf : AnalyticAt ℝ f p) :
    directional v (cubicProduct f) p =
      3 * p.2 ^ 2 * v.2 * f p + p.2 ^ 3 * directional v f p := by
  have hs : HasFDerivAt (fun q : E × ℝ => q.2 ^ 3)
      ((3 * p.2 ^ 2) • ContinuousLinearMap.snd ℝ E ℝ) p := by
    convert (hasDerivAt_pow 3 p.2).comp_hasFDerivAt p
      (hasFDerivAt_snd : HasFDerivAt (fun q : E × ℝ => q.2) (ContinuousLinearMap.snd ℝ E ℝ) p) using 1 <;> norm_num
  unfold directional cubicProduct
  rw [(hs.mul hf.differentiableAt.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  change p.2 ^ 3 * (fderiv ℝ f p) v + f p * (3 * p.2 ^ 2 * v.2) = _
  ring

theorem euler_cubicProduct {f : E × ℝ → ℝ} {p : E × ℝ}
    (hf : AnalyticAt ℝ f p) :
    euler (cubicProduct f) p = cubicProduct (liftedEuler f) p := by
  rw [euler, directional_cubicProduct hf]
  dsimp [cubicProduct, liftedEuler, euler]
  ring

theorem parameter_cubicProduct {f : E × ℝ → ℝ} {p : E × ℝ}
    (hf : AnalyticAt ℝ f p) (v : E) :
    directional (v, 0) (cubicProduct f) p = cubicProduct (directional (v, 0) f) p := by
  rw [directional_cubicProduct hf]
  simp [cubicProduct]

theorem directional_congr_on_open {f g : E × ℝ → ℝ} {s : Set (E × ℝ)}
    (hs : IsOpen s) (he : EqOn f g s) {p : E × ℝ} (hp : p ∈ s) (v : E × ℝ) :
    directional v f p = directional v g p := by
  have hv : f =ᶠ[𝓝 p] g := by
    filter_upwards [hs.mem_nhds hp] with q hq
    exact he hq
  exact congrArg (fun L : (E × ℝ) →L[ℝ] ℝ => L v) hv.fderiv_eq

theorem analyticAt_iterated_liftedEuler {f : E × ℝ → ℝ} {p : E × ℝ}
    (hf : AnalyticAt ℝ f p) (n : ℕ) : AnalyticAt ℝ ((liftedEuler^[n]) f) p := by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [Function.iterate_succ_apply'] using analyticAt_liftedEuler ih

theorem analyticAt_parameterDerivatives {f : E × ℝ → ℝ} {p : E × ℝ}
    (hf : AnalyticAt ℝ f p) (vs : List E) : AnalyticAt ℝ (parameterDerivatives vs f) p := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact analyticAt_directional ih (v, 0)

theorem iterated_euler_cubicProduct {f : E × ℝ → ℝ} {s : Set (E × ℝ)}
    (hs : IsOpen s) (hf : AnalyticOnNhd ℝ f s) (n : ℕ) :
    EqOn ((euler^[n]) (cubicProduct f)) (cubicProduct ((liftedEuler^[n]) f)) s := by
  induction n with
  | zero => intro p _; rfl
  | succ n ih =>
      intro p hp
      simp only [Function.iterate_succ_apply']
      calc
        euler ((euler^[n]) (cubicProduct f)) p =
            euler (cubicProduct ((liftedEuler^[n]) f)) p := by
          change p.2 * directional (0, 1) ((euler^[n]) (cubicProduct f)) p = _
          rw [directional_congr_on_open hs ih hp]
          rfl
        _ = cubicProduct (liftedEuler ((liftedEuler^[n]) f)) p :=
          euler_cubicProduct (analyticAt_iterated_liftedEuler (hf p hp) n)

theorem parameterDerivatives_cubicProduct {f : E × ℝ → ℝ} {s : Set (E × ℝ)}
    (hs : IsOpen s) (hf : AnalyticOnNhd ℝ f s) (vs : List E) :
    EqOn (parameterDerivatives vs (cubicProduct f))
      (cubicProduct (parameterDerivatives vs f)) s := by
  induction vs with
  | nil => intro p _; rfl
  | cons v vs ih =>
      intro p hp
      rw [parameterDerivatives, directional_congr_on_open hs ih hp]
      exact parameter_cubicProduct (analyticAt_parameterDerivatives (hf p hp) vs) v

theorem parameterDerivatives_congr_on_open {f g : E × ℝ → ℝ} {s : Set (E × ℝ)}
    (hs : IsOpen s) (he : EqOn f g s) (vs : List E) :
    EqOn (parameterDerivatives vs f) (parameterDerivatives vs g) s := by
  induction vs with
  | nil => exact he
  | cons v vs ih =>
      intro p hp
      exact directional_congr_on_open hs ih hp (v, 0)

theorem euler_iterate_congr_on_open {f g : E × ℝ → ℝ} {s : Set (E × ℝ)}
    (hs : IsOpen s) (he : EqOn f g s) (n : ℕ) : EqOn ((euler^[n]) f) ((euler^[n]) g) s := by
  induction n with
  | zero => exact he
  | succ n ih =>
      intro p hp
      simp only [Function.iterate_succ_apply', euler]
      rw [directional_congr_on_open hs ih hp]

theorem mixed_euler_cubic_factorization {f g : E × ℝ → ℝ} {s : Set (E × ℝ)}
    (hs : IsOpen s) (hg : AnalyticOnNhd ℝ g s) (he : EqOn f (cubicProduct g) s)
    (vs : List E) (n : ℕ) :
    EqOn (parameterDerivatives vs ((euler^[n]) f))
      (cubicProduct (parameterDerivatives vs ((liftedEuler^[n]) g))) s := by
  have h1 := euler_iterate_congr_on_open hs he n
  have h2 := iterated_euler_cubicProduct hs hg n
  have h3 := parameterDerivatives_congr_on_open hs (h1.trans h2) vs
  exact h3.trans (parameterDerivatives_cubicProduct hs
    (fun p hp => analyticAt_iterated_liftedEuler (hg p hp) n) vs)

/-- A quantified compact cubic bound for every actual fixed sequence of
parameter derivatives and every actual fixed Euler order. -/
theorem uniform_mixed_euler_cubic_bound {f g : E × ℝ → ℝ} {s K : Set (E × ℝ)}
    (hs : IsOpen s) (hg : AnalyticOnNhd ℝ g s) (he : EqOn f (cubicProduct g) s)
    (hK : IsCompact K) (hKs : K ⊆ s) (vs : List E) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K,
      |parameterDerivatives vs ((euler^[n]) f) p| ≤ C * |p.2| ^ 3 := by
  let q := parameterDerivatives vs ((liftedEuler^[n]) g)
  have hq : AnalyticOnNhd ℝ q s := fun p hp =>
    analyticAt_parameterDerivatives (analyticAt_iterated_liftedEuler (hg p hp) n) vs
  obtain ⟨M, hM⟩ := hK.bddAbove_image
    (fun p hp => (hq p (hKs hp)).continuousAt.abs.continuousWithinAt)
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro p hp
  rw [mixed_euler_cubic_factorization hs hg he vs n (hKs hp)]
  rw [cubicProduct, abs_mul, abs_pow]
  have hb : |q p| ≤ |M| + 1 :=
    (hM ⟨p, hp, rfl⟩).trans (by linarith [le_abs_self M])
  calc
    |p.2| ^ 3 * |q p| ≤ |p.2| ^ 3 * (|M| + 1) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg (abs_nonneg _) _)
    _ = (|M| + 1) * |p.2| ^ 3 := mul_comm _ _

end LeanVerification.CubicDerivatives
