import LeanVerification.PositiveDCompletion.LowerCone

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

def lowerCubeF (a t : ℝ) : ℝ := 1+(a-1)*t
def lowerCubeB (a t : ℝ) : ℝ :=
  2*a^2*t^2-a^2*t-4*a*t^2+6*a*t-a-5*t+5
def lowerCubeC (a t : ℝ) : ℝ := 2+2*(a-1)*t+a*(a-1)*t^2
def lowerCubeG (a t : ℝ) : ℝ :=
  a^5*t^3-4*a^4*t^3+a^4*t^2+6*a^3*t^3-5*a^3*t^2-4*a^2*t^3+
    13*a^2*t^2+a*t^3-9*a*t^2+8*a*t+2*t^2-4*t+2
def lowerCubeD (a t : ℝ) : ℝ := a^2*t^2*lowerCubeB a t
def lowerRhoDen (a t : ℝ) : ℝ := lowerCubeF a t*lowerCubeD a t
def lowerRhoNum (a t u : ℝ) : ℝ :=
  a*lowerCubeD a t+(1-t)^2*lowerCubeG a t*u

theorem lowerCubeB_identity (a t : ℝ) :
    lowerEnvelopeB a (lowerCubeF a t)=(a-1)^2*lowerCubeB a t := by
  unfold lowerEnvelopeB lowerCubeF lowerCubeB
  ring

theorem lowerCubeG_identity (a t : ℝ) :
    (lowerCubeF a t)^3*lowerCubeC a t-a*lowerCubeD a t=(1-t)^2*lowerCubeG a t := by
  unfold lowerCubeF lowerCubeC lowerCubeD lowerCubeB lowerCubeG
  ring

theorem lowerCubeB_pos {a t : ℝ} (ha : 1<a) (hau : a<3)
    (ht : 0<t) (htu : t<1) : 0<lowerCubeB a t := by
  have ham : 0<a-1 := by linarith
  have hf : 1<lowerCubeF a t := by
    unfold lowerCubeF
    linarith [mul_pos ham ht]
  have hfa : lowerCubeF a t<a := by
    unfold lowerCubeF
    nlinarith [mul_lt_mul_of_pos_left htu ham]
  have hB := lowerEnvelopeB_pos ha hau hf hfa
  rw [lowerCubeB_identity] at hB
  exact pos_of_mul_pos_right hB (sq_pos_of_pos ham).le

theorem lowerRhoDen_pos {a t : ℝ} (ha : 1<a) (hau : a<3)
    (ht : 0<t) (htu : t<1) : 0<lowerRhoDen a t := by
  have hB := lowerCubeB_pos ha hau ht htu
  have ham : 0<a-1 := by linarith
  have ha0 : 0<a := by linarith
  unfold lowerRhoDen lowerCubeD lowerCubeF
  positivity

theorem lowerEnvelope_cube {a t : ℝ} (ha : a≠1) (ha0 : a≠0)
    (ht : t≠0) (hB : lowerCubeB a t≠0) :
    lowerEnvelope a (lowerCubeF a t)=
      (lowerCubeF a t)^2*lowerCubeC a t/lowerCubeD a t := by
  have ham : a-1≠0 := sub_ne_zero.mpr ha
  have hf : lowerCubeF a t-1=(a-1)*t := by unfold lowerCubeF; ring
  have hC : a*(lowerCubeF a t)^2+a-2*lowerCubeF a t=(a-1)*lowerCubeC a t := by
    unfold lowerCubeF lowerCubeC
    ring
  unfold lowerEnvelope
  rw [lowerCubeB_identity,hf,hC]
  unfold lowerCubeD
  field_simp [ha0,ham,ht,hB]
  ring

theorem lowerRho_cube {a t u : ℝ} (ha : 1<a) (hau : a<3)
    (ht : 0<t) (htu : t<1) :
    lowerRhoNum a t u/lowerRhoDen a t=
      a/lowerCubeF a t+(lowerEnvelope a (lowerCubeF a t)-a/lowerCubeF a t)*u := by
  have hB := lowerCubeB_pos ha hau ht htu
  have ha0 : 0<a := by linarith
  have ham : 0<a-1 := by linarith
  have hf : 0<lowerCubeF a t := by unfold lowerCubeF; positivity
  have hd : 0<lowerCubeD a t := by unfold lowerCubeD; positivity
  rw [lowerEnvelope_cube (ne_of_gt ha) ha0.ne' ht.ne' hB.ne']
  unfold lowerRhoNum lowerRhoDen
  rw [←lowerCubeG_identity]
  field_simp [hf.ne',hd.ne']
  ring

theorem lower_correlated_coordinates {a f rho : ℝ}
    (ha : 1<a) (hau : a<3) (hf : 1<f) (hfa : f<a)
    (hr : a/f<rho) (hru : rho<lowerEnvelope a f) :
    ∃ x t u : ℝ, 0<x ∧ x<1 ∧ 0<t ∧ t<1 ∧ 0<u ∧ u<1 ∧
      a=1+2*x ∧ f=lowerCubeF a t ∧ rho=lowerRhoNum a t u/lowerRhoDen a t := by
  obtain ⟨hx,hxu,ht,htu,hax,hfx⟩ := lower_cube_coordinates ha hau hf hfa
  let t := (f-1)/(a-1)
  have hfe : lowerCubeF a t=f := by
    dsimp only [lowerCubeF,t]
    have hneq : a-1≠0 := by linarith
    field_simp [hneq]
    <;> ring
  have hgap : 0<lowerEnvelope a f-a/f := by linarith
  let u := (rho-a/f)/(lowerEnvelope a f-a/f)
  have hu : 0<u := div_pos (sub_pos.mpr hr) hgap
  have huu : u<1 := (div_lt_one hgap).mpr (by linarith)
  refine ⟨(a-1)/2,t,u,hx,hxu,ht,htu,hu,huu,hax.symm,hfe.symm,?_⟩
  rw [lowerRho_cube ha hau ht htu,hfe]
  dsimp only [u]
  rw [mul_div_cancel₀ _ hgap.ne']
  ring

end LeanVerification.PositiveDCompletion
