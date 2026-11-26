import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks00
import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks01
import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks02
import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks03
import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks04
import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks05
import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks06
import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks07
import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks08
import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks09
import LeanVerification.PositiveDCompletion.LowerCertificate09Blocks10
import LeanVerification.PositiveDCompletion.LowerCertificate09Coefficient0
import LeanVerification.PositiveDCompletion.LowerCertificate09Coefficient1
import LeanVerification.PositiveDCompletion.LowerCertificate09Coefficient2
import LeanVerification.PositiveDCompletion.LowerCertificate09Coefficient3
import LeanVerification.PositiveDCompletion.LowerCertificate09Coefficient4
import LeanVerification.PositiveDCompletion.LowerCertificate09Coefficient5
import LeanVerification.PositiveDCompletion.LowerCertificate09Coefficient6

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCertificate09_identity (x t u : ℝ) :
    lowerAtom09 x t u=lowerCertificate09 x t u := by
  unfold lowerCertificate09 lowerAtom09
  rw [lowerCertificate09Block00_identity,lowerCertificate09Block01_identity,lowerCertificate09Block02_identity,lowerCertificate09Block03_identity,lowerCertificate09Block04_identity,lowerCertificate09Block05_identity,lowerCertificate09Block06_identity,lowerCertificate09Block07_identity,lowerCertificate09Block08_identity,lowerCertificate09Block09_identity,lowerCertificate09Block10_identity,lowerCertificate09Block11_identity,lowerCertificate09Block12_identity,lowerCertificate09Block13_identity,lowerCertificate09Block14_identity,lowerCertificate09Block15_identity,lowerCertificate09Block16_identity,lowerCertificate09Block17_identity,lowerCertificate09Block18_identity,lowerCertificate09Block19_identity,lowerCertificate09Block20_identity,lowerCertificate09Block21_identity,lowerCertificate09Block22_identity,lowerCertificate09Block23_identity,lowerCertificate09Block24_identity,lowerCertificate09Block25_identity,lowerCertificate09Block26_identity,lowerCertificate09Block27_identity,lowerCertificate09Block28_identity,lowerCertificate09Block29_identity,lowerCertificate09Block30_identity,lowerCertificate09Block31_identity,lowerCertificate09Block32_identity,lowerCertificate09Block33_identity,lowerCertificate09Block34_identity,lowerCertificate09Block35_identity,lowerCertificate09Block36_identity,lowerCertificate09Block37_identity,lowerCertificate09Block38_identity,lowerCertificate09Block39_identity,lowerCertificate09Block40_identity,lowerCertificate09Block41_identity,lowerCertificate09Block42_identity,lowerCertificate09Block43_identity,lowerCertificate09Block44_identity,lowerCertificate09Block45_identity,lowerCertificate09Block46_identity,lowerCertificate09Block47_identity,lowerCertificate09Block48_identity,lowerCertificate09Block49_identity,lowerCertificate09Block50_identity,lowerCertificate09Block51_identity,lowerAtom09Coeff0_identity,lowerAtom09Coeff1_identity,lowerAtom09Coeff2_identity,lowerAtom09Coeff3_identity,lowerAtom09Coeff4_identity,lowerAtom09Coeff5_identity,lowerAtom09Coeff6_identity]
  ring

theorem lowerAtom09_pos {x t u : ℝ} (hx : 0<x) (hxu : x<1) (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :
    0<lowerAtom09 x t u := by
  rw [lowerCertificate09_identity]
  have hb0 := lowerCertificate09Block00_pos ht htu hu huu
  have hw0 := lowerCertificate09Weight00_pos hx hxu
  have hb1 := lowerCertificate09Block01_pos ht htu hu huu
  have hw1 := lowerCertificate09Weight01_pos hx hxu
  have hb2 := lowerCertificate09Block02_pos ht htu hu huu
  have hw2 := lowerCertificate09Weight02_pos hx hxu
  have hb3 := lowerCertificate09Block03_pos ht htu hu huu
  have hw3 := lowerCertificate09Weight03_pos hx hxu
  have hb4 := lowerCertificate09Block04_pos ht htu hu huu
  have hw4 := lowerCertificate09Weight04_pos hx hxu
  have hb5 := lowerCertificate09Block05_pos ht htu hu huu
  have hw5 := lowerCertificate09Weight05_pos hx hxu
  have hb6 := lowerCertificate09Block06_pos ht htu hu huu
  have hw6 := lowerCertificate09Weight06_pos hx hxu
  have hb7 := lowerCertificate09Block07_pos ht htu hu huu
  have hw7 := lowerCertificate09Weight07_pos hx hxu
  have hb8 := lowerCertificate09Block08_pos ht htu hu huu
  have hw8 := lowerCertificate09Weight08_pos hx hxu
  have hb9 := lowerCertificate09Block09_pos ht htu hu huu
  have hw9 := lowerCertificate09Weight09_pos hx hxu
  have hb10 := lowerCertificate09Block10_pos ht htu hu huu
  have hw10 := lowerCertificate09Weight10_pos hx hxu
  have hb11 := lowerCertificate09Block11_pos ht htu hu huu
  have hw11 := lowerCertificate09Weight11_pos hx hxu
  have hb12 := lowerCertificate09Block12_pos ht htu hu huu
  have hw12 := lowerCertificate09Weight12_pos hx hxu
  have hb13 := lowerCertificate09Block13_pos ht htu hu huu
  have hw13 := lowerCertificate09Weight13_pos hx hxu
  have hb14 := lowerCertificate09Block14_pos ht htu hu huu
  have hw14 := lowerCertificate09Weight14_pos hx hxu
  have hb15 := lowerCertificate09Block15_pos ht htu hu huu
  have hw15 := lowerCertificate09Weight15_pos hx hxu
  have hb16 := lowerCertificate09Block16_pos ht htu hu huu
  have hw16 := lowerCertificate09Weight16_pos hx hxu
  have hb17 := lowerCertificate09Block17_pos ht htu hu huu
  have hw17 := lowerCertificate09Weight17_pos hx hxu
  have hb18 := lowerCertificate09Block18_pos ht htu hu huu
  have hw18 := lowerCertificate09Weight18_pos hx hxu
  have hb19 := lowerCertificate09Block19_pos ht htu hu huu
  have hw19 := lowerCertificate09Weight19_pos hx hxu
  have hb20 := lowerCertificate09Block20_pos ht htu hu huu
  have hw20 := lowerCertificate09Weight20_pos hx hxu
  have hb21 := lowerCertificate09Block21_pos ht htu hu huu
  have hw21 := lowerCertificate09Weight21_pos hx hxu
  have hb22 := lowerCertificate09Block22_pos ht htu hu huu
  have hw22 := lowerCertificate09Weight22_pos hx hxu
  have hb23 := lowerCertificate09Block23_pos ht htu hu huu
  have hw23 := lowerCertificate09Weight23_pos hx hxu
  have hb24 := lowerCertificate09Block24_pos ht htu hu huu
  have hw24 := lowerCertificate09Weight24_pos hx hxu
  have hb25 := lowerCertificate09Block25_pos ht htu hu huu
  have hw25 := lowerCertificate09Weight25_pos hx hxu
  have hb26 := lowerCertificate09Block26_pos ht htu hu huu
  have hw26 := lowerCertificate09Weight26_pos hx hxu
  have hb27 := lowerCertificate09Block27_pos ht htu hu huu
  have hw27 := lowerCertificate09Weight27_pos hx hxu
  have hb28 := lowerCertificate09Block28_pos ht htu hu huu
  have hw28 := lowerCertificate09Weight28_pos hx hxu
  have hb29 := lowerCertificate09Block29_pos ht htu hu huu
  have hw29 := lowerCertificate09Weight29_pos hx hxu
  have hb30 := lowerCertificate09Block30_pos ht htu hu huu
  have hw30 := lowerCertificate09Weight30_pos hx hxu
  have hb31 := lowerCertificate09Block31_pos ht htu hu huu
  have hw31 := lowerCertificate09Weight31_pos hx hxu
  have hb32 := lowerCertificate09Block32_pos ht htu hu huu
  have hw32 := lowerCertificate09Weight32_pos hx hxu
  have hb33 := lowerCertificate09Block33_pos ht htu hu huu
  have hw33 := lowerCertificate09Weight33_pos hx hxu
  have hb34 := lowerCertificate09Block34_pos ht htu hu huu
  have hw34 := lowerCertificate09Weight34_pos hx hxu
  have hb35 := lowerCertificate09Block35_pos ht htu hu huu
  have hw35 := lowerCertificate09Weight35_pos hx hxu
  have hb36 := lowerCertificate09Block36_pos ht htu hu huu
  have hw36 := lowerCertificate09Weight36_pos hx hxu
  have hb37 := lowerCertificate09Block37_pos ht htu hu huu
  have hw37 := lowerCertificate09Weight37_pos hx hxu
  have hb38 := lowerCertificate09Block38_pos ht htu hu huu
  have hw38 := lowerCertificate09Weight38_pos hx hxu
  have hb39 := lowerCertificate09Block39_pos ht htu hu huu
  have hw39 := lowerCertificate09Weight39_pos hx hxu
  have hb40 := lowerCertificate09Block40_pos ht htu hu huu
  have hw40 := lowerCertificate09Weight40_pos hx hxu
  have hb41 := lowerCertificate09Block41_pos ht htu hu huu
  have hw41 := lowerCertificate09Weight41_pos hx hxu
  have hb42 := lowerCertificate09Block42_pos ht htu hu huu
  have hw42 := lowerCertificate09Weight42_pos hx hxu
  have hb43 := lowerCertificate09Block43_pos ht htu hu huu
  have hw43 := lowerCertificate09Weight43_pos hx hxu
  have hb44 := lowerCertificate09Block44_pos ht htu hu huu
  have hw44 := lowerCertificate09Weight44_pos hx hxu
  have hb45 := lowerCertificate09Block45_pos ht htu hu huu
  have hw45 := lowerCertificate09Weight45_pos hx hxu
  have hb46 := lowerCertificate09Block46_pos ht htu hu huu
  have hw46 := lowerCertificate09Weight46_pos hx hxu
  have hb47 := lowerCertificate09Block47_pos ht htu hu huu
  have hw47 := lowerCertificate09Weight47_pos hx hxu
  have hb48 := lowerCertificate09Block48_pos ht htu hu huu
  have hw48 := lowerCertificate09Weight48_pos hx hxu
  have hb49 := lowerCertificate09Block49_pos ht htu hu huu
  have hw49 := lowerCertificate09Weight49_pos hx hxu
  have hb50 := lowerCertificate09Block50_pos ht htu hu huu
  have hw50 := lowerCertificate09Weight50_pos hx hxu
  have hb51 := lowerCertificate09Block51_pos ht htu hu huu
  have hw51 := lowerCertificate09Weight51_pos hx hxu
  unfold lowerCertificate09
  positivity

end LeanVerification.PositiveDCompletion
