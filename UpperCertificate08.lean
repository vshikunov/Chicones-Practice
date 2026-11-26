import LeanVerification.PositiveDCompletion.UpperPolynomial08
import LeanVerification.PositiveDCompletion.UpperCertificate08Blocks00
import LeanVerification.PositiveDCompletion.UpperCertificate08Blocks01
import LeanVerification.PositiveDCompletion.UpperCertificate08Blocks02
import LeanVerification.PositiveDCompletion.UpperCertificate08Blocks03
import LeanVerification.PositiveDCompletion.UpperCertificate08Blocks04
import LeanVerification.PositiveDCompletion.UpperCertificate08Blocks05
import LeanVerification.PositiveDCompletion.UpperCertificate08Coefficient0
import LeanVerification.PositiveDCompletion.UpperCertificate08Coefficient1
import LeanVerification.PositiveDCompletion.UpperCertificate08Coefficient2
import LeanVerification.PositiveDCompletion.UpperCertificate08Coefficient3
import LeanVerification.PositiveDCompletion.UpperCertificate08Coefficient4
import LeanVerification.PositiveDCompletion.UpperCertificate08Coefficient5
import LeanVerification.PositiveDCompletion.UpperCertificate08Coefficient6

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperCertificate08_identity (a t z : ℝ) :
    upperAtom08 a t z=upperCertificate08 a t z := by
  unfold upperCertificate08 upperAtom08
  rw [upperCertificate08Block00_identity,upperCertificate08Block01_identity,upperCertificate08Block02_identity,upperCertificate08Block03_identity,upperCertificate08Block04_identity,upperCertificate08Block05_identity,upperCertificate08Block06_identity,upperCertificate08Block07_identity,upperCertificate08Block08_identity,upperCertificate08Block09_identity,upperCertificate08Block10_identity,upperCertificate08Block11_identity,upperCertificate08Block12_identity,upperCertificate08Block13_identity,upperCertificate08Block14_identity,upperCertificate08Block15_identity,upperCertificate08Block16_identity,upperCertificate08Block17_identity,upperCertificate08Block18_identity,upperCertificate08Block19_identity,upperCertificate08Block20_identity,upperCertificate08Block21_identity,upperCertificate08Block22_identity,upperCertificate08Block23_identity,upperCertificate08Block24_identity,upperCertificate08Block25_identity,upperCertificate08Block26_identity,upperAtom08Coeff0_identity,upperAtom08Coeff1_identity,upperAtom08Coeff2_identity,upperAtom08Coeff3_identity,upperAtom08Coeff4_identity,upperAtom08Coeff5_identity,upperAtom08Coeff6_identity]
  ring

theorem upperAtom08_pos {a t z : ℝ} (ha : 0<a) (hau : a<1)
    (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) : 0<upperAtom08 a t z := by
  rw [upperCertificate08_identity]
  have hb0 := upperCertificate08Block00_pos ht htu hz hzu
  have hw0 := upperCertificate08Weight00_pos ha hau
  have hb1 := upperCertificate08Block01_pos ht htu hz hzu
  have hw1 := upperCertificate08Weight01_pos ha hau
  have hb2 := upperCertificate08Block02_pos ht htu hz hzu
  have hw2 := upperCertificate08Weight02_pos ha hau
  have hb3 := upperCertificate08Block03_pos ht htu hz hzu
  have hw3 := upperCertificate08Weight03_pos ha hau
  have hb4 := upperCertificate08Block04_pos ht htu hz hzu
  have hw4 := upperCertificate08Weight04_pos ha hau
  have hb5 := upperCertificate08Block05_pos ht htu hz hzu
  have hw5 := upperCertificate08Weight05_pos ha hau
  have hb6 := upperCertificate08Block06_pos ht htu hz hzu
  have hw6 := upperCertificate08Weight06_pos ha hau
  have hb7 := upperCertificate08Block07_pos ht htu hz hzu
  have hw7 := upperCertificate08Weight07_pos ha hau
  have hb8 := upperCertificate08Block08_pos ht htu hz hzu
  have hw8 := upperCertificate08Weight08_pos ha hau
  have hb9 := upperCertificate08Block09_pos ht htu hz hzu
  have hw9 := upperCertificate08Weight09_pos ha hau
  have hb10 := upperCertificate08Block10_pos ht htu hz hzu
  have hw10 := upperCertificate08Weight10_pos ha hau
  have hb11 := upperCertificate08Block11_pos ht htu hz hzu
  have hw11 := upperCertificate08Weight11_pos ha hau
  have hb12 := upperCertificate08Block12_pos ht htu hz hzu
  have hw12 := upperCertificate08Weight12_pos ha hau
  have hb13 := upperCertificate08Block13_pos ht htu hz hzu
  have hw13 := upperCertificate08Weight13_pos ha hau
  have hb14 := upperCertificate08Block14_pos ht htu hz hzu
  have hw14 := upperCertificate08Weight14_pos ha hau
  have hb15 := upperCertificate08Block15_pos ht htu hz hzu
  have hw15 := upperCertificate08Weight15_pos ha hau
  have hb16 := upperCertificate08Block16_pos ht htu hz hzu
  have hw16 := upperCertificate08Weight16_pos ha hau
  have hb17 := upperCertificate08Block17_pos ht htu hz hzu
  have hw17 := upperCertificate08Weight17_pos ha hau
  have hb18 := upperCertificate08Block18_pos ht htu hz hzu
  have hw18 := upperCertificate08Weight18_pos ha hau
  have hb19 := upperCertificate08Block19_pos ht htu hz hzu
  have hw19 := upperCertificate08Weight19_pos ha hau
  have hb20 := upperCertificate08Block20_pos ht htu hz hzu
  have hw20 := upperCertificate08Weight20_pos ha hau
  have hb21 := upperCertificate08Block21_pos ht htu hz hzu
  have hw21 := upperCertificate08Weight21_pos ha hau
  have hb22 := upperCertificate08Block22_pos ht htu hz hzu
  have hw22 := upperCertificate08Weight22_pos ha hau
  have hb23 := upperCertificate08Block23_pos ht htu hz hzu
  have hw23 := upperCertificate08Weight23_pos ha hau
  have hb24 := upperCertificate08Block24_pos ht htu hz hzu
  have hw24 := upperCertificate08Weight24_pos ha hau
  have hb25 := upperCertificate08Block25_pos ht htu hz hzu
  have hw25 := upperCertificate08Weight25_pos ha hau
  have hb26 := upperCertificate08Block26_pos ht htu hz hzu
  have hw26 := upperCertificate08Weight26_pos ha hau
  unfold upperCertificate08
  positivity

theorem upperNum08_pos {a f rho : ℝ} (ha : 0<a) (hau : a<1)
    (haf : a<f) (hf : f<1) (hr : 0<rho) (hru : rho<1)
    (hprod : f*rho<a) : 0<upperNum08 a f rho := by
  obtain ⟨ht,htu,hfeq⟩ := upper_cube_coordinate hau haf hf
  have hac : 0<1-a := by linarith
  have hf0 : 0<f := ha.trans haf
  obtain ⟨hu,huu,hueq⟩ := upper_correlated_coordinate ha hf0 hr hprod
  have hp := upperAtom08_pos ha hau ht htu hu huu
  have he := upperNum08_map a ((f-a)/(1-a)) (f*rho/a)
  rw [hfeq,hueq,←upperNum08_clear] at he
  have hpos : 0<f^(6 : ℕ)*upperNum08 a f rho := by rw [he];exact mul_pos (pow_pos hac _) hp
  exact pos_of_mul_pos_right hpos (pow_pos hf0 _).le

end LeanVerification.PositiveDCompletion
