import LeanVerification.PositiveDCompletion.SignedRegular
import LeanVerification.ReflectedWedgeCompletion.ModelNumeratorIdentities
import LeanVerification.ReflectedWedgeCompletion.ModelFractionAlgebra
import LeanVerification.ReflectedWedgeCompletion.DiagonalJetModel

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 48000000
set_option maxRecDepth 50000
namespace SignedRegular
variable {a f rho omega : ℝ} (h : SignedRegular a f rho)
include h

theorem modelAlpha1_eq_jet : modelAlpha1 a f rho=jetAlpha1 a f rho := by
  unfold modelAlpha1 jetAlpha1 modelG
  ring

theorem modelAlpha2_eq_jet : modelAlpha2 a f rho=jetAlpha2 a f rho := by
  unfold modelAlpha2 jetAlpha2 modelG
  ring

theorem modelAlpha3_eq_jet : modelAlpha3 a f rho=jetAlpha3 a f rho := by
  unfold modelAlpha3 jetAlpha3 modelG
  ring

theorem modelAlpha4_eq_jet : modelAlpha4 a f rho=jetAlpha4 a f rho := by
  unfold modelAlpha4 jetAlpha4 modelG
  ring

theorem modelEll_eq_jet : modelEll a f rho=jetEll a f rho := by
  unfold modelEll jetEll modelG
  simp only [div_eq_mul_inv,mul_inv,sub_eq_add_neg,mul_comm rho (a^2),neg_one_mul]
  ring

theorem modelPoleFlow_eq_jet : modelPoleFlow a f rho=jetPoleFlow a f rho := by
  have hg := h.g_ne
  have hj := h.j_ne
  have hGN : (-1 : ℝ)+rho*a^2≠0 := by
    convert neg_ne_zero.mpr hg using 1 <;> unfold modelG <;> ring
  have hGP : (1 : ℝ)+(-1)*(rho*a^2)≠0 := by
    convert hg using 1 <;> unfold modelG <;> ring
  unfold modelPoleFlow jetPoleFlow
  unfold modelG at *
  field_simp (disch := simp [hg,hj,hGN,hGP]) [hg,hj,hGN,hGP]
  <;> ring

theorem modelFZero_eq_jet : modelFZero a f rho=jetFZero a f rho := by
  have hA2 : (2:ℝ)*f^2+(-2)*(rho*a^2)=2*modelA a f rho := by
    unfold modelA
    ring
  unfold modelFZero jetFZero
  rw [hA2]
  ring

theorem modelRZero_eq_jet : modelRZero a f rho=jetRZero a f rho := by
  unfold modelRZero jetRZero modelG
  rfl

theorem modelL_transportN : modelL a f rho omega=
    transportN a f rho omega/(modelG a rho*(1+f)) := by
  have hg := h.g_ne
  have hj := h.j_ne
  unfold modelL modelEll transportN
  field_simp (disch := simp [hg,hj]) [hg,hj]
  unfold modelG
  ring

theorem modelLambda_transportF (hn : transportN a f rho omega≠0) :
    modelLambda a f rho omega*diagonalTransportF a f rho=transportF a f rho omega := by
  have hg := h.g_ne
  have hj := h.j_ne
  unfold modelLambda
  rw [h.modelL_transportN]
  unfold diagonalTransportF modelSigma transportF
  rw [show (1:ℝ)+(-1)*(rho*a^2)=modelG a rho by unfold modelG; ring]
  unfold modelG at *
  field_simp (disch := simp [hg,hj,hn]) [hg,hj,hn]
  <;> ring

theorem modelLambda_transportRho (hn : transportN a f rho omega≠0) :
    modelLambda a f rho omega*diagonalTransportRho a f rho=transportRho a f rho omega := by
  have hg := h.g_ne
  have hj := h.j_ne
  unfold modelLambda
  rw [h.modelL_transportN]
  unfold diagonalTransportRho modelSigma transportRho
  unfold modelG at *
  field_simp (disch := simp [h.a_ne,hg,hj,hn]) [h.a_ne,hg,hj,hn]
  <;> ring

theorem modelOmega_transport (hn : transportN a f rho omega≠0) :
    -2*modelM a f rho*omega*(1+omega)/modelL a f rho omega=transportOmega a f rho omega := by
  have hg := h.g_ne
  have hj := h.j_ne
  rw [h.modelL_transportN]
  unfold modelM transportOmega
  unfold modelG at *
  field_simp (disch := simp [hg,hj,hn]) [hg,hj,hn]
  <;> ring

theorem jetCurvature_eq_model (hw : 1+omega≠0) (hn : transportN a f rho omega≠0) : jetCurvature a f rho omega=modelF a f rho omega := by
  have hj := h.j_ne
  have hg := h.g_ne
  have hA := h.A_ne
  have hfa := h.f_a_ne
  have hfu := h.f_one_ne
  have hru := h.rho_one_ne
  have hAP : f^2+(-1)*(rho*a^2)=modelA a f rho := by unfold modelA; ring
  have hW4 : (4:ℝ)+4*omega=4*(1+omega) := by ring
  have hNP : (1+f)*(1+(-1)*(rho*a^2))+(a*rho)*(omega*(1+(-1)*(a*f)))=
      transportN a f rho omega := by unfold transportN; ring
  have hraw : jetCurvature a f rho omega=
      modelCurvatureNumerator a f rho omega/(4*(1+omega)*modelA a f rho*(transportN a f rho omega)^3) := by
    change ((4+4*omega)⁻¹*(f^2+(-1)*(rho*a^2))⁻¹)*
      ((((1+f)*(1+(-1)*(rho*a^2))+(a*rho)*(omega*(1+(-1)*(a*f))))^3)⁻¹*
      modelCurvatureNumerator a f rho omega) = _
    simp only [hAP,hW4,hNP,div_eq_mul_inv,mul_inv]
    ring
  let B := 2*(f-a)*(1-f)*(1-rho)
  have hB : B≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hfa) hfu) hru
  have hFform : modelF a f rho omega =
      (1+a)*B/(4*modelA a f rho)*
        (1-weakNum00 a f rho/(B*(1+f)*(modelG a rho)^2)*omega-
          weakNum01 a f rho/(B*(1+f)^2*(modelG a rho)^2)*omega^2-
          weakNum02 a f rho/(B*(1+f)^3*(modelG a rho)^3)*omega^3-
          weakNum03 a f rho/(B*(1+f)^3*(modelG a rho)^3)*omega^4)/
        ((1+omega)*(transportN a f rho omega/(modelG a rho*(1+f)))^3) := by
    unfold modelF
    rw [h.modelL_transportN]
    unfold modelFZero modelPsi compactPsi modelAlpha1 modelAlpha2 modelAlpha3 modelAlpha4
    dsimp only [B]
    ring
  have hnum : modelCurvatureNumerator a f rho omega = (1+a)*
      (B*(1+f)^3*(modelG a rho)^3-
        weakNum00 a f rho*(1+f)^2*modelG a rho*omega-
        weakNum01 a f rho*(1+f)*modelG a rho*omega^2-
        weakNum02 a f rho*omega^3-weakNum03 a f rho*omega^4) := by
    rw [model_curvature_numerator_identity]
    dsimp only [B,modelG]
    ring
  have hx := curvature_fraction_assembly B (1+f) (modelG a rho) (modelA a f rho)
    (1+omega) (transportN a f rho omega) (1+a) omega
    (weakNum00 a f rho) (weakNum01 a f rho) (weakNum02 a f rho) (weakNum03 a f rho)
    hB hj hg hA hw hn
  rw [hraw,hFform,hx,← hnum]

theorem modelL_ne (hn : transportN a f rho omega≠0) : modelL a f rho omega≠0 := by
  rw [h.modelL_transportN]
  exact div_ne_zero hn (mul_ne_zero h.g_ne h.j_ne)

end SignedRegular
end LeanVerification.PositiveDCompletion
