import LeanVerification.HolomorphicCompactFamily
import Mathlib.MeasureTheory.Integral.TorusIntegral

/-!
# The Cauchy formula in finitely many complex parameters

The product formula is proved by the actual scalar Cauchy formula in each
coordinate and the checked torus-integral Fubini identity.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal NNReal

namespace LeanVerification.PolydiscCauchy

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

def closedPolydisc {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ i, z i ∈ closedBall (c i) (R i)}

def openPolydisc {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ i, z i ∈ ball (c i) (R i)}

def distinguishedBoundary {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ i, z i ∈ sphere (c i) (R i)}

theorem boundary_subset_closed {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) :
    distinguishedBoundary c R ⊆ closedPolydisc c R :=
  fun _ hz i => sphere_subset_closedBall (hz i)

theorem open_subset_closed {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) :
    openPolydisc c R ⊆ closedPolydisc c R :=
  fun _ hz i => ball_subset_closedBall (hz i)

theorem continuous_torusMap {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) :
    Continuous (torusMap c R) := by
  unfold torusMap
  fun_prop

theorem torusMap_mem_boundary {n : ℕ} (c : Fin n → ℂ) {R : Fin n → ℝ}
    (hR : ∀ i, 0 ≤ R i) (θ : Fin n → ℝ) :
    torusMap c R θ ∈ distinguishedBoundary c R := by
  intro i
  exact circleMap_mem_sphere (c i) (hR i) (θ i)

theorem continuousOn_cauchyKernel {n : ℕ} {c z : Fin n → ℂ} {R : Fin n → ℝ}
    (hz : z ∈ openPolydisc c R) :
    ContinuousOn (fun w => ∏ i, (w i - z i)⁻¹) (distinguishedBoundary c R) := by
  apply continuousOn_finset_prod
  intro i _
  apply ((continuous_apply i).continuousOn.sub continuousOn_const).inv₀
  intro w hw
  exact sub_ne_zero.mpr (ne_of_mem_of_not_mem (hw i) (ne_of_lt (hz i)))

theorem torusIntegrable_cauchy {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {c z : Fin n → ℂ} {R : Fin n → ℝ} (hR : ∀ i, 0 ≤ R i)
    (hf : ContinuousOn f (closedPolydisc c R)) (hz : z ∈ openPolydisc c R) :
    TorusIntegrable (fun w => (∏ i, (w i - z i)⁻¹) * f w) c R := by
  have hc := ((continuousOn_cauchyKernel hz).mul
    (hf.mono (boundary_subset_closed c R))).comp_continuous
      (continuous_torusMap c R) (torusMap_mem_boundary c hR)
  exact hc.continuousOn.integrableOn_compact isCompact_Icc

/-- Product Cauchy formula. Coordinate differentiability is required on the
closed polydisc, as follows automatically when that closed polydisc lies inside
a holomorphic domain. -/
theorem torusIntegral_cauchy {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {c z : Fin n → ℂ} {R : Fin n → ℝ} (hR : ∀ i, 0 < R i)
    (hc : ContinuousOn f (closedPolydisc c R))
    (hd : ∀ w ∈ closedPolydisc c R, ∀ i : Fin n,
      DifferentiableAt ℂ (fun u => f (Function.update w i u)) (w i))
    (hz : z ∈ openPolydisc c R) :
    (∯ w in T(c, R), (∏ i, (w i - z i)⁻¹) * f w) =
      (2 * Real.pi * Complex.I : ℂ) ^ n * f z := by
  induction n with
  | zero =>
      simp only [torusIntegral_dim0, Fin.prod_univ_zero, pow_zero, one_mul]
      congr 1
      exact Subsingleton.elim _ _
  | succ n ih =>
      have hinner (x : ℂ) (hx : x ∈ sphere (c 0) (R 0)) :
          (∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ),
            (∏ i : Fin (n + 1), ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * f (Fin.cons x y)) =
            (x - z 0)⁻¹ * ((2 * Real.pi * Complex.I : ℂ) ^ n *
              f (Fin.cons x (z ∘ Fin.succ))) := by
        have hcons (y : Fin n → ℂ) (hy : y ∈ closedPolydisc (c ∘ Fin.succ) (R ∘ Fin.succ)) :
            Fin.cons x y ∈ closedPolydisc c R := by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact sphere_subset_closedBall hx
          · exact hy j
        have hct : ContinuousOn (fun y => f (Fin.cons x y))
            (closedPolydisc (c ∘ Fin.succ) (R ∘ Fin.succ)) :=
          hc.comp (show ContinuousOn (fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ))
            (closedPolydisc (c ∘ Fin.succ) (R ∘ Fin.succ)) from
              (show Continuous (fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) from by
                apply continuous_pi
                intro i
                refine Fin.cases ?_ (fun j => ?_) i
                · simpa only [Fin.cons_zero] using (continuous_const : Continuous (fun _ : Fin n → ℂ => x))
                · simpa only [Fin.cons_succ] using (continuous_apply j : Continuous (fun y : Fin n → ℂ => y j))
              ).continuousOn) hcons
        have hdt : ∀ y ∈ closedPolydisc (c ∘ Fin.succ) (R ∘ Fin.succ), ∀ i : Fin n,
            DifferentiableAt ℂ (fun u => f (Fin.cons x (Function.update y i u))) (y i) := by
          intro y hy i
          simpa only [Fin.cons_update, Fin.cons_succ] using hd _ (hcons y hy) i.succ
        have he := ih (f := fun y => f (Fin.cons x y))
          (c := c ∘ Fin.succ) (z := z ∘ Fin.succ) (R := R ∘ Fin.succ)
          (fun i => hR i.succ) hct hdt (fun i => hz i.succ)
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        simp_rw [mul_assoc]
        rw [torusIntegral_const_mul]
        simpa only [Function.comp_def, mul_assoc] using
          congrArg (fun a : ℂ => (x - z 0)⁻¹ * a) he
      rw [torusIntegral_succ (torusIntegrable_cauchy (fun i => (hR i).le) hc hz)]
      rw [circleIntegral.integral_congr (hR 0).le hinner]
      have hct : ContinuousOn (fun x => f (Fin.cons x (z ∘ Fin.succ)))
          (closedBall (c 0) (R 0)) := by
        apply hc.comp (show ContinuousOn (fun x : ℂ => (Fin.cons x (z ∘ Fin.succ) : Fin (n + 1) → ℂ))
          (closedBall (c 0) (R 0)) from
            (show Continuous (fun x : ℂ => (Fin.cons x (z ∘ Fin.succ) : Fin (n + 1) → ℂ)) from by
              apply continuous_pi
              intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · simpa only [Fin.cons_zero] using (continuous_id : Continuous (fun x : ℂ => x))
              · simpa only [Fin.cons_succ] using (continuous_const : Continuous (fun _ : ℂ => z j.succ))
            ).continuousOn)
        intro x hx i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hx
        · exact ball_subset_closedBall (hz j.succ)
      have hdt : ∀ x ∈ ball (c 0) (R 0) \ (∅ : Set ℂ),
          DifferentiableAt ℂ (fun u => f (Fin.cons u (z ∘ Fin.succ))) x := by
        intro x hx
        have hcons : Fin.cons x (z ∘ Fin.succ) ∈ closedPolydisc c R := by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact ball_subset_closedBall hx.1
          · exact ball_subset_closedBall (hz j.succ)
        simpa only [Fin.update_cons_zero, Fin.cons_zero] using hd _ hcons 0
      have he := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        countable_empty (hz 0) hct hdt
      simp only [smul_eq_mul] at he
      have hzeta : Fin.cons (z 0) (z ∘ Fin.succ) = z := Fin.cons_self_tail z
      rw [hzeta] at he
      calc
        (∮ x in C(c 0, R 0), (x - z 0)⁻¹ *
            ((2 * Real.pi * Complex.I : ℂ) ^ n * f (Fin.cons x (z ∘ Fin.succ)))) =
            (2 * Real.pi * Complex.I : ℂ) ^ n *
              ∮ x in C(c 0, R 0), (x - z 0)⁻¹ * f (Fin.cons x (z ∘ Fin.succ)) := by
          have hfun : (fun x : ℂ => (x - z 0)⁻¹ *
              ((2 * Real.pi * Complex.I : ℂ) ^ n * f (Fin.cons x (z ∘ Fin.succ)))) =
              (fun x : ℂ => (2 * Real.pi * Complex.I : ℂ) ^ n *
                ((x - z 0)⁻¹ * f (Fin.cons x (z ∘ Fin.succ)))) := by
            funext x
            ring
          rw [hfun]
          exact circleIntegral.integral_const_mul _ _ _ _
        _ = (2 * Real.pi * Complex.I : ℂ) ^ (n + 1) * f z := by
          rw [he, pow_succ]
          ring

end LeanVerification.PolydiscCauchy
