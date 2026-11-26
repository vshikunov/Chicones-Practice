import LeanVerification.PositiveDCompletion.UpperCertificate07Blocks00
import LeanVerification.PositiveDCompletion.UpperCertificate07Blocks01
import LeanVerification.PositiveDCompletion.UpperCertificate07Blocks02
import LeanVerification.PositiveDCompletion.UpperCertificate07Blocks03
import LeanVerification.PositiveDCompletion.UpperCertificate07Coefficient0
import LeanVerification.PositiveDCompletion.UpperCertificate07Coefficient1
import LeanVerification.PositiveDCompletion.UpperCertificate07Coefficient2
import LeanVerification.PositiveDCompletion.UpperCertificate07Coefficient3
import LeanVerification.PositiveDCompletion.UpperCertificate07Coefficient4
import LeanVerification.PositiveDCompletion.UpperCertificate07Coefficient5
import LeanVerification.PositiveDCompletion.UpperCertificate07Coefficient6

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperCertificate07_identity (a t z : ℝ) :
    upperAtom07 a t z=upperCertificate07 a t z := by
  unfold upperCertificate07 upperAtom07
  rw [upperCertificate07Block00_identity,upperCertificate07Block01_identity,upperCertificate07Block02_identity,upperCertificate07Block03_identity,upperCertificate07Block04_identity,upperCertificate07Block05_identity,upperCertificate07Block06_identity,upperCertificate07Block07_identity,upperCertificate07Block08_identity,upperCertificate07Block09_identity,upperCertificate07Block10_identity,upperCertificate07Block11_identity,upperCertificate07Block12_identity,upperCertificate07Block13_identity,upperCertificate07Block14_identity,upperCertificate07Block15_identity,upperCertificate07Block16_identity,upperCertificate07Block17_identity,upperCertificate07Block18_identity,upperCertificate07Block19_identity,upperAtom07Coeff0_identity,upperAtom07Coeff1_identity,upperAtom07Coeff2_identity,upperAtom07Coeff3_identity,upperAtom07Coeff4_identity,upperAtom07Coeff5_identity,upperAtom07Coeff6_identity]
  ring

theorem upperAtom07_pos {a t z : ℝ} (ha : 0<a) (hau : a<1)
    (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) : 0<upperAtom07 a t z := by
  rw [upperCertificate07_identity]
  have hb0 := upperCertificate07Block00_pos ht htu hz hzu
  have hw0 := upperCertificate07Weight00_pos ha hau
  have hb1 := upperCertificate07Block01_pos ht htu hz hzu
  have hw1 := upperCertificate07Weight01_pos ha hau
  have hb2 := upperCertificate07Block02_pos ht htu hz hzu
  have hw2 := upperCertificate07Weight02_pos ha hau
  have hb3 := upperCertificate07Block03_pos ht htu hz hzu
  have hw3 := upperCertificate07Weight03_pos ha hau
  have hb4 := upperCertificate07Block04_pos ht htu hz hzu
  have hw4 := upperCertificate07Weight04_pos ha hau
  have hb5 := upperCertificate07Block05_pos ht htu hz hzu
  have hw5 := upperCertificate07Weight05_pos ha hau
  have hb6 := upperCertificate07Block06_pos ht htu hz hzu
  have hw6 := upperCertificate07Weight06_pos ha hau
  have hb7 := upperCertificate07Block07_pos ht htu hz hzu
  have hw7 := upperCertificate07Weight07_pos ha hau
  have hb8 := upperCertificate07Block08_pos ht htu hz hzu
  have hw8 := upperCertificate07Weight08_pos ha hau
  have hb9 := upperCertificate07Block09_pos ht htu hz hzu
  have hw9 := upperCertificate07Weight09_pos ha hau
  have hb10 := upperCertificate07Block10_pos ht htu hz hzu
  have hw10 := upperCertificate07Weight10_pos ha hau
  have hb11 := upperCertificate07Block11_pos ht htu hz hzu
  have hw11 := upperCertificate07Weight11_pos ha hau
  have hb12 := upperCertificate07Block12_pos ht htu hz hzu
  have hw12 := upperCertificate07Weight12_pos ha hau
  have hb13 := upperCertificate07Block13_pos ht htu hz hzu
  have hw13 := upperCertificate07Weight13_pos ha hau
  have hb14 := upperCertificate07Block14_pos ht htu hz hzu
  have hw14 := upperCertificate07Weight14_pos ha hau
  have hb15 := upperCertificate07Block15_pos ht htu hz hzu
  have hw15 := upperCertificate07Weight15_pos ha hau
  have hb16 := upperCertificate07Block16_pos ht htu hz hzu
  have hw16 := upperCertificate07Weight16_pos ha hau
  have hb17 := upperCertificate07Block17_pos ht htu hz hzu
  have hw17 := upperCertificate07Weight17_pos ha hau
  have hb18 := upperCertificate07Block18_pos ht htu hz hzu
  have hw18 := upperCertificate07Weight18_pos ha hau
  have hb19 := upperCertificate07Block19_pos ht htu hz hzu
  have hw19 := upperCertificate07Weight19_pos ha hau
  unfold upperCertificate07
  positivity

theorem upperNum07_pos {a f rho : ℝ} (ha : 0<a) (hau : a<1)
    (haf : a<f) (hf : f<1) (hr : 0<rho) (hru : rho<1) : 0<upperNum07 a f rho := by
  obtain ⟨ht,htu,hfeq⟩ := upper_cube_coordinate hau haf hf
  have hac : 0<1-a := by linarith
  have hp := upperAtom07_pos ha hau ht htu hr hru
  have he := upperNum07_map a ((f-a)/(1-a)) rho
  rw [hfeq] at he
  rw [he]
  exact mul_pos (pow_pos hac _) hp

end LeanVerification.PositiveDCompletion
