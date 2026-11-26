import LeanVerification.PositiveDCompletion.SignedRegular
import LeanVerification.ReflectedWedgeCompletion.SourceCoefficientPolynomial01
import LeanVerification.ReflectedWedgeCompletion.SourceCoefficientPolynomial02
import LeanVerification.ReflectedWedgeCompletion.SourceCoefficientPolynomial03
import LeanVerification.ReflectedWedgeCompletion.SourceCoefficientPolynomial04
import LeanVerification.ReflectedWedgeCompletion.SourceCoefficientPolynomial05

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
namespace SignedRegular
variable {a f rho : ℝ} (h : SignedRegular a f rho)
include h

theorem sourceCoefficient1_identity : modelV1 a f rho=
    2*modelM a f rho*modelAlpha1 a f rho-jetDAlpha1 a f rho := by
  have ha := h.a_ne
  have hj := h.j_ne
  have hg := h.g_ne
  have hfa := h.f_a_ne
  have hfu := h.f_one_ne
  have hru := h.rho_one_ne
  rw [sourceDAlpha1_fraction]
  unfold modelV1 modelE1 modelM modelAlpha1 
  rw [sourceCoefficient1_numerator]
  unfold sourceDAlphaDenominator1 modelG at *
  generalize weakNum00 a f rho=A1
  generalize sourceDAlphaNumerator1 a f rho=N1
  generalize f-a=q at *
  generalize 1-f=t at *
  generalize 1+f=j at *
  generalize 1-rho=r at *
  generalize 1-a^2*rho=g at *
  field_simp [ha,hj,hg,hfa,hfu,hru]
  <;> ring

theorem sourceCoefficient2_identity : modelV2 a f rho=
    4*modelM a f rho*modelAlpha2 a f rho-jetDAlpha2 a f rho+2*modelM a f rho*modelAlpha1 a f rho-modelSigma f*jetDAlpha1 a f rho := by
  have ha := h.a_ne
  have hj := h.j_ne
  have hg := h.g_ne
  have hfa := h.f_a_ne
  have hfu := h.f_one_ne
  have hru := h.rho_one_ne
  rw [sourceDAlpha2_fraction,sourceDAlpha1_fraction]
  unfold modelV2 modelE2 modelM modelSigma modelAlpha2 modelAlpha1 
  rw [sourceCoefficient2_numerator]
  unfold sourceDAlphaDenominator2 sourceDAlphaDenominator1 modelG at *
  generalize weakNum01 a f rho=A2
  generalize sourceDAlphaNumerator2 a f rho=N2
  generalize weakNum00 a f rho=A1
  generalize sourceDAlphaNumerator1 a f rho=N1
  generalize f-a=q at *
  generalize 1-f=t at *
  generalize 1+f=j at *
  generalize 1-rho=r at *
  generalize 1-a^2*rho=g at *
  field_simp [ha,hj,hg,hfa,hfu,hru]
  <;> ring

theorem sourceCoefficient3_identity : modelV3 a f rho=
    6*modelM a f rho*modelAlpha3 a f rho-jetDAlpha3 a f rho+4*modelM a f rho*modelAlpha2 a f rho-modelSigma f*jetDAlpha2 a f rho := by
  have ha := h.a_ne
  have hj := h.j_ne
  have hg := h.g_ne
  have hfa := h.f_a_ne
  have hfu := h.f_one_ne
  have hru := h.rho_one_ne
  rw [sourceDAlpha3_fraction,sourceDAlpha2_fraction]
  unfold modelV3 modelE3 modelM modelSigma modelAlpha3 modelAlpha2 
  rw [sourceCoefficient3_numerator]
  unfold sourceDAlphaDenominator3 sourceDAlphaDenominator2 modelG at *
  generalize weakNum02 a f rho=A3
  generalize sourceDAlphaNumerator3 a f rho=N3
  generalize weakNum01 a f rho=A2
  generalize sourceDAlphaNumerator2 a f rho=N2
  generalize f-a=q at *
  generalize 1-f=t at *
  generalize 1+f=j at *
  generalize 1-rho=r at *
  generalize 1-a^2*rho=g at *
  field_simp [ha,hj,hg,hfa,hfu,hru]
  <;> ring

theorem sourceCoefficient4_identity : modelV4 a f rho=
    8*modelM a f rho*modelAlpha4 a f rho-jetDAlpha4 a f rho+6*modelM a f rho*modelAlpha3 a f rho-modelSigma f*jetDAlpha3 a f rho := by
  have ha := h.a_ne
  have hj := h.j_ne
  have hg := h.g_ne
  have hfa := h.f_a_ne
  have hfu := h.f_one_ne
  have hru := h.rho_one_ne
  rw [sourceDAlpha4_fraction,sourceDAlpha3_fraction]
  unfold modelV4 modelE4 modelM modelSigma modelAlpha4 modelAlpha3 
  rw [sourceCoefficient4_numerator]
  unfold sourceDAlphaDenominator4 sourceDAlphaDenominator3 modelG at *
  generalize weakNum03 a f rho=A4
  generalize sourceDAlphaNumerator4 a f rho=N4
  generalize weakNum02 a f rho=A3
  generalize sourceDAlphaNumerator3 a f rho=N3
  generalize f-a=q at *
  generalize 1-f=t at *
  generalize 1+f=j at *
  generalize 1-rho=r at *
  generalize 1-a^2*rho=g at *
  field_simp [ha,hj,hg,hfa,hfu,hru]
  <;> ring

theorem sourceCoefficient5_identity : modelV5 a f rho=
    8*modelM a f rho*modelAlpha4 a f rho-modelSigma f*jetDAlpha4 a f rho := by
  have ha := h.a_ne
  have hj := h.j_ne
  have hg := h.g_ne
  have hfa := h.f_a_ne
  have hfu := h.f_one_ne
  have hru := h.rho_one_ne
  rw [sourceDAlpha4_fraction]
  unfold modelV5 modelE5 modelM modelSigma modelAlpha4 
  rw [sourceCoefficient5_numerator]
  unfold sourceDAlphaDenominator4 modelG at *
  generalize weakNum03 a f rho=A4
  generalize sourceDAlphaNumerator4 a f rho=N4
  generalize f-a=q at *
  generalize 1-f=t at *
  generalize 1+f=j at *
  generalize 1-rho=r at *
  generalize 1-a^2*rho=g at *
  field_simp [ha,hj,hg,hfa,hfu,hru]
  <;> ring

end SignedRegular
end LeanVerification.PositiveDCompletion
