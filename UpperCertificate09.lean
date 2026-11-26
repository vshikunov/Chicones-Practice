import LeanVerification.PositiveDCompletion.UpperPolynomial09
import LeanVerification.PositiveDCompletion.UpperCertificate09Blocks00
import LeanVerification.PositiveDCompletion.UpperCertificate09Blocks01
import LeanVerification.PositiveDCompletion.UpperCertificate09Blocks02
import LeanVerification.PositiveDCompletion.UpperCertificate09Blocks03
import LeanVerification.PositiveDCompletion.UpperCertificate09Blocks04
import LeanVerification.PositiveDCompletion.UpperCertificate09Blocks05
import LeanVerification.PositiveDCompletion.UpperCertificate09Coefficient0
import LeanVerification.PositiveDCompletion.UpperCertificate09Coefficient1
import LeanVerification.PositiveDCompletion.UpperCertificate09Coefficient2
import LeanVerification.PositiveDCompletion.UpperCertificate09Coefficient3
import LeanVerification.PositiveDCompletion.UpperCertificate09Coefficient4
import LeanVerification.PositiveDCompletion.UpperCertificate09Coefficient5
import LeanVerification.PositiveDCompletion.UpperCertificate09Coefficient6

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperCertificate09_identity (a t z : ℝ) :
    upperAtom09 a t z=upperCertificate09 a t z := by
  unfold upperCertificate09 upperAtom09
  rw [upperCertificate09Block00_identity,upperCertificate09Block01_identity,upperCertificate09Block02_identity,upperCertificate09Block03_identity,upperCertificate09Block04_identity,upperCertificate09Block05_identity,upperCertificate09Block06_identity,upperCertificate09Block07_identity,upperCertificate09Block08_identity,upperCertificate09Block09_identity,upperCertificate09Block10_identity,upperCertificate09Block11_identity,upperCertificate09Block12_identity,upperCertificate09Block13_identity,upperCertificate09Block14_identity,upperCertificate09Block15_identity,upperCertificate09Block16_identity,upperCertificate09Block17_identity,upperCertificate09Block18_identity,upperCertificate09Block19_identity,upperCertificate09Block20_identity,upperCertificate09Block21_identity,upperCertificate09Block22_identity,upperCertificate09Block23_identity,upperCertificate09Block24_identity,upperCertificate09Block25_identity,upperCertificate09Block26_identity,upperCertificate09Block27_identity,upperAtom09Coeff0_identity,upperAtom09Coeff1_identity,upperAtom09Coeff2_identity,upperAtom09Coeff3_identity,upperAtom09Coeff4_identity,upperAtom09Coeff5_identity,upperAtom09Coeff6_identity]
  ring

theorem upperAtom09_pos {a t z : ℝ} (ha : 0<a) (hau : a<1)
    (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) : 0<upperAtom09 a t z := by
  rw [upperCertificate09_identity]
  have hb0 := upperCertificate09Block00_pos ht htu hz hzu
  have hw0 := upperCertificate09Weight00_pos ha hau
  have hb1 := upperCertificate09Block01_pos ht htu hz hzu
  have hw1 := upperCertificate09Weight01_pos ha hau
  have hb2 := upperCertificate09Block02_pos ht htu hz hzu
  have hw2 := upperCertificate09Weight02_pos ha hau
  have hb3 := upperCertificate09Block03_pos ht htu hz hzu
  have hw3 := upperCertificate09Weight03_pos ha hau
  have hb4 := upperCertificate09Block04_pos ht htu hz hzu
  have hw4 := upperCertificate09Weight04_pos ha hau
  have hb5 := upperCertificate09Block05_pos ht htu hz hzu
  have hw5 := upperCertificate09Weight05_pos ha hau
  have hb6 := upperCertificate09Block06_pos ht htu hz hzu
  have hw6 := upperCertificate09Weight06_pos ha hau
  have hb7 := upperCertificate09Block07_pos ht htu hz hzu
  have hw7 := upperCertificate09Weight07_pos ha hau
  have hb8 := upperCertificate09Block08_pos ht htu hz hzu
  have hw8 := upperCertificate09Weight08_pos ha hau
  have hb9 := upperCertificate09Block09_pos ht htu hz hzu
  have hw9 := upperCertificate09Weight09_pos ha hau
  have hb10 := upperCertificate09Block10_pos ht htu hz hzu
  have hw10 := upperCertificate09Weight10_pos ha hau
  have hb11 := upperCertificate09Block11_pos ht htu hz hzu
  have hw11 := upperCertificate09Weight11_pos ha hau
  have hb12 := upperCertificate09Block12_pos ht htu hz hzu
  have hw12 := upperCertificate09Weight12_pos ha hau
  have hb13 := upperCertificate09Block13_pos ht htu hz hzu
  have hw13 := upperCertificate09Weight13_pos ha hau
  have hb14 := upperCertificate09Block14_pos ht htu hz hzu
  have hw14 := upperCertificate09Weight14_pos ha hau
  have hb15 := upperCertificate09Block15_pos ht htu hz hzu
  have hw15 := upperCertificate09Weight15_pos ha hau
  have hb16 := upperCertificate09Block16_pos ht htu hz hzu
  have hw16 := upperCertificate09Weight16_pos ha hau
  have hb17 := upperCertificate09Block17_pos ht htu hz hzu
  have hw17 := upperCertificate09Weight17_pos ha hau
  have hb18 := upperCertificate09Block18_pos ht htu hz hzu
  have hw18 := upperCertificate09Weight18_pos ha hau
  have hb19 := upperCertificate09Block19_pos ht htu hz hzu
  have hw19 := upperCertificate09Weight19_pos ha hau
  have hb20 := upperCertificate09Block20_pos ht htu hz hzu
  have hw20 := upperCertificate09Weight20_pos ha hau
  have hb21 := upperCertificate09Block21_pos ht htu hz hzu
  have hw21 := upperCertificate09Weight21_pos ha hau
  have hb22 := upperCertificate09Block22_pos ht htu hz hzu
  have hw22 := upperCertificate09Weight22_pos ha hau
  have hb23 := upperCertificate09Block23_pos ht htu hz hzu
  have hw23 := upperCertificate09Weight23_pos ha hau
  have hb24 := upperCertificate09Block24_pos ht htu hz hzu
  have hw24 := upperCertificate09Weight24_pos ha hau
  have hb25 := upperCertificate09Block25_pos ht htu hz hzu
  have hw25 := upperCertificate09Weight25_pos ha hau
  have hb26 := upperCertificate09Block26_pos ht htu hz hzu
  have hw26 := upperCertificate09Weight26_pos ha hau
  have hb27 := upperCertificate09Block27_pos ht htu hz hzu
  have hw27 := upperCertificate09Weight27_pos ha hau
  unfold upperCertificate09
  positivity

theorem upperNum09_pos {a f rho : ℝ} (ha : 0<a) (hau : a<1)
    (haf : a<f) (hf : f<1) (hr : 0<rho) (hru : rho<1)
    (hprod : f*rho<a) : 0<upperNum09 a f rho := by
  obtain ⟨ht,htu,hfeq⟩ := upper_cube_coordinate hau haf hf
  have hac : 0<1-a := by linarith
  have hf0 : 0<f := ha.trans haf
  obtain ⟨hu,huu,hueq⟩ := upper_correlated_coordinate ha hf0 hr hprod
  have hp := upperAtom09_pos ha hau ht htu hu huu
  have he := upperNum09_map a ((f-a)/(1-a)) (f*rho/a)
  rw [hfeq,hueq,←upperNum09_clear] at he
  have hpos : 0<f^(6 : ℕ)*upperNum09 a f rho := by rw [he];exact mul_pos (pow_pos hac _) hp
  exact pos_of_mul_pos_right hpos (pow_pos hf0 _).le

end LeanVerification.PositiveDCompletion
