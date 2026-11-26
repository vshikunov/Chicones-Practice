import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Extending an interior derivative to the endpoints of a closed interval

If a function and its prescribed derivative are continuous on a nondegenerate
closed interval, and the prescribed derivative is correct in the interior,
then it is also the one-sided derivative at both endpoints. The conclusions
are derivatives within the closed interval, so no extension of the function
beyond that interval is assumed.
-/

namespace LeanVerification.EndpointDerivative

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous interior derivative extends to the left endpoint as a
derivative within the closed interval. -/
theorem hasDerivWithinAt_Icc_left_of_interior
    {f g : ℝ → E} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) :
    HasDerivWithinAt f (g a) (Icc a b) a := by
  have hdiff : DifferentiableOn ℝ f (Ioo a b) := fun x hx =>
    (hd x hx).differentiableAt.differentiableWithinAt
  have hfcont : ContinuousWithinAt f (Ioo a b) a :=
    (hf a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self
  have hgcont : Tendsto g (𝓝[>] a) (𝓝 (g a)) := by
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT hab] using
      (hg a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self
  have hderiv : Tendsto (fun x => deriv f x) (𝓝[>] a) (𝓝 (g a)) := by
    apply hgcont.congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    exact (hd x hx).deriv.symm
  exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hfcont
    (Ioo_mem_nhdsGT hab) hderiv).mono Icc_subset_Ici_self

/-- A continuous interior derivative extends to the right endpoint as a
derivative within the closed interval. -/
theorem hasDerivWithinAt_Icc_right_of_interior
    {f g : ℝ → E} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) :
    HasDerivWithinAt f (g b) (Icc a b) b := by
  have hdiff : DifferentiableOn ℝ f (Ioo a b) := fun x hx =>
    (hd x hx).differentiableAt.differentiableWithinAt
  have hfcont : ContinuousWithinAt f (Ioo a b) b :=
    (hf b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self
  have hgcont : Tendsto g (𝓝[<] b) (𝓝 (g b)) := by
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hab] using
      (hg b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self
  have hderiv : Tendsto (fun x => deriv f x) (𝓝[<] b) (𝓝 (g b)) := by
    apply hgcont.congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    exact (hd x hx).deriv.symm
  exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hfcont
    (Ioo_mem_nhdsLT hab) hderiv).mono Icc_subset_Iic_self

/-- The derivative prescribed continuously on a closed interval agrees with
the derivative within that interval at every point, including its endpoints. -/
theorem hasDerivWithinAt_Icc_of_interior
    {f g : ℝ → E} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x)
    {x : ℝ} (hx : x ∈ Icc a b) :
    HasDerivWithinAt f (g x) (Icc a b) x := by
  by_cases hxa : x = a
  · subst x
    exact hasDerivWithinAt_Icc_left_of_interior hab hf hg hd
  by_cases hxb : x = b
  · subst x
    exact hasDerivWithinAt_Icc_right_of_interior hab hf hg hd
  exact (hd x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa),
    lt_of_le_of_ne hx.2 hxb⟩).hasDerivWithinAt

end LeanVerification.EndpointDerivative
