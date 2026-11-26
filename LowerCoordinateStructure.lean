import LeanVerification.PositiveDCompletion.LowerCoordinates

/-! Small exact structure lemmas for the lower correlated coordinates.

The existing physical and certificate sources are unchanged. These lemmas
exhibit a positive factorization already present in their coordinate data.
-/

noncomputable section
namespace LeanVerification.PositiveDCompletion

theorem lowerCubeB_positive_form (a t : ℝ) :
    lowerCubeB a t =
      (5 - a) * (1 - t)^2 +
        (5 - a) * (a + 1) * t * (1 - t) + a * (a + 1) * t^2 := by
  unfold lowerCubeB
  ring

theorem lowerCubeB_pos_of_lt_five {a t : ℝ} (ha : 0 < a) (hau : a < 5)
    (ht : 0 < t) (htu : t < 1) : 0 < lowerCubeB a t := by
  have hfive : 0 < 5 - a := sub_pos.mpr hau
  have hcomp : 0 < 1 - t := sub_pos.mpr htu
  rw [lowerCubeB_positive_form]
  positivity

theorem lowerCubeG_factorization (a t : ℝ) :
    lowerCubeG a t =
      a * (a - 1)^4 * t^3 +
        (a * (a - 1) * ((a - 2)^2 + 5) + 2) * t^2 +
        (8 * a - 4) * t + 2 := by
  unfold lowerCubeG
  ring

theorem lowerCubeG_ge_two {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) :
    2 ≤ lowerCubeG a t := by
  rw [lowerCubeG_factorization]
  have ha0 : 0 ≤ a := by linarith
  have ham : 0 ≤ a - 1 := by linarith
  have hlinear : 0 ≤ 8 * a - 4 := by linarith
  have h0 : 0 ≤ a * (a - 1)^4 * t^3 := by positivity
  have h1 : 0 ≤ (a * (a - 1) * ((a - 2)^2 + 5) + 2) * t^2 := by positivity
  have h2 : 0 ≤ (8 * a - 4) * t := mul_nonneg hlinear ht
  linarith

theorem lowerCubeG_pos {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) :
    0 < lowerCubeG a t :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (lowerCubeG_ge_two ha ht)

theorem lowerEnvelope_cube_gap {a t : ℝ} (ha : 1 < a) (hau : a < 3)
    (ht : 0 < t) (htu : t < 1) :
    lowerEnvelope a (lowerCubeF a t) - a / lowerCubeF a t =
      (1 - t)^2 * lowerCubeG a t / lowerRhoDen a t := by
  have hB := lowerCubeB_pos ha hau ht htu
  have ha0 : 0 < a := by linarith
  have ham : 0 < a - 1 := by linarith
  have hf : 0 < lowerCubeF a t := by unfold lowerCubeF; positivity
  have hd : 0 < lowerCubeD a t := by unfold lowerCubeD; positivity
  calc
    _ = ((lowerCubeF a t)^3 * lowerCubeC a t - a * lowerCubeD a t) /
        (lowerCubeF a t * lowerCubeD a t) := by
      rw [lowerEnvelope_cube (ne_of_gt ha) ha0.ne' ht.ne' hB.ne']
      field_simp [hf.ne', hd.ne']
      <;> ring
    _ = _ := by rw [lowerCubeG_identity]; rfl

theorem lowerEnvelope_cube_gap_pos {a t : ℝ} (ha : 1 < a) (hau : a < 3)
    (ht : 0 < t) (htu : t < 1) :
    0 < lowerEnvelope a (lowerCubeF a t) - a / lowerCubeF a t := by
  rw [lowerEnvelope_cube_gap ha hau ht htu]
  exact div_pos
    (mul_pos (sq_pos_of_pos (sub_pos.mpr htu)) (lowerCubeG_pos ha.le ht.le))
    (lowerRhoDen_pos ha hau ht htu)

end LeanVerification.PositiveDCompletion
