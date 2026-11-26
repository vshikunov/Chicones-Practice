import LeanVerification.PositiveDCompletion.UpperPolynomial00

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 48000000
set_option maxRecDepth 50000

def upperCertificate00Block00 (t z : ℝ) : ℝ := ((t^3)*((1-t)*(((1 : ℝ)*((1-z)^2))+(((2 : ℝ)*(z*(1-z)))+((1 : ℝ)*(z^2))))))

theorem upperCertificate00Block00_identity (t z : ℝ) :
    upperCertificate00Block00 t z=(((-1 : ℝ)*(t^4))+((1 : ℝ)*(t^3))) := by
  have hz3 : (((1 : ℝ)*((1-z)^2))+(((2 : ℝ)*(z*(1-z)))+((1 : ℝ)*(z^2)))) = (1 : ℝ) := by ring
  unfold upperCertificate00Block00
  simp only [hz3]
  ring

theorem upperCertificate00Block00_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate00Block00 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate00Block00
  positivity

def upperCertificate00Block01 (t z : ℝ) : ℝ := (((t^2)*(((1-t)^2)*(((3 : ℝ)*((1-z)^2))+(((5 : ℝ)*(z*(1-z)))+((2 : ℝ)*(z^2))))))+(((t^3)*((1-t)*(((8 : ℝ)*((1-z)^2))+(((17 : ℝ)*(z*(1-z)))+((9 : ℝ)*(z^2))))))+((t^4)*(((2 : ℝ)*(z*(1-z)))+((2 : ℝ)*(z^2))))))

theorem upperCertificate00Block01_identity (t z : ℝ) :
    upperCertificate00Block01 t z=((((-5 : ℝ)*(t^4))+((3 : ℝ)*((t^3)*z)))+(((2 : ℝ)*(t^3))+(((-1 : ℝ)*((t^2)*z))+((3 : ℝ)*(t^2))))) := by
  have hz2 : (((3 : ℝ)*((1-z)^2))+(((5 : ℝ)*(z*(1-z)))+((2 : ℝ)*(z^2)))) = (((-1 : ℝ)*z)+(3 : ℝ)) := by ring
  have hz3 : (((8 : ℝ)*((1-z)^2))+(((17 : ℝ)*(z*(1-z)))+((9 : ℝ)*(z^2)))) = (((1 : ℝ)*z)+(8 : ℝ)) := by ring
  have hz4 : (((2 : ℝ)*(z*(1-z)))+((2 : ℝ)*(z^2))) = ((2 : ℝ)*z) := by ring
  unfold upperCertificate00Block01
  simp only [hz2,hz3,hz4]
  ring

theorem upperCertificate00Block01_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate00Block01 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate00Block01
  positivity

def upperCertificate00Block02 (t z : ℝ) : ℝ := (((t*(((1-t)^3)*(((3 : ℝ)*((1-z)^2))+((3 : ℝ)*(z*(1-z))))))+((t^2)*(((1-t)^2)*(((21 : ℝ)*((1-z)^2))+(((31 : ℝ)*(z*(1-z)))+((10 : ℝ)*(z^2)))))))+(((t^3)*((1-t)*(((26 : ℝ)*((1-z)^2))+(((51 : ℝ)*(z*(1-z)))+((25 : ℝ)*(z^2))))))+((t^4)*(((6 : ℝ)*(z*(1-z)))+((6 : ℝ)*(z^2))))))

theorem upperCertificate00Block02_identity (t z : ℝ) :
    upperCertificate00Block02 t z=(((((-1 : ℝ)*((t^4)*z))+((-8 : ℝ)*(t^4)))+(((12 : ℝ)*((t^3)*z))+((-7 : ℝ)*(t^3))))+((((-2 : ℝ)*((t^2)*z))+((12 : ℝ)*(t^2)))+(((-3 : ℝ)*(t*z))+((3 : ℝ)*t)))) := by
  have hz1 : (((3 : ℝ)*((1-z)^2))+((3 : ℝ)*(z*(1-z)))) = (((-3 : ℝ)*z)+(3 : ℝ)) := by ring
  have hz2 : (((21 : ℝ)*((1-z)^2))+(((31 : ℝ)*(z*(1-z)))+((10 : ℝ)*(z^2)))) = (((-11 : ℝ)*z)+(21 : ℝ)) := by ring
  have hz3 : (((26 : ℝ)*((1-z)^2))+(((51 : ℝ)*(z*(1-z)))+((25 : ℝ)*(z^2)))) = (((-1 : ℝ)*z)+(26 : ℝ)) := by ring
  have hz4 : (((6 : ℝ)*(z*(1-z)))+((6 : ℝ)*(z^2))) = ((6 : ℝ)*z) := by ring
  unfold upperCertificate00Block02
  simp only [hz1,hz2,hz3,hz4]
  ring

theorem upperCertificate00Block02_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate00Block02 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate00Block02
  positivity

def upperCertificate00Block03 (t z : ℝ) : ℝ := (((((1-t)^4)*((1 : ℝ)*((1-z)^2)))+(t*(((1-t)^3)*(((18 : ℝ)*((1-z)^2))+((13 : ℝ)*(z*(1-z)))))))+(((t^2)*(((1-t)^2)*(((57 : ℝ)*((1-z)^2))+(((63 : ℝ)*(z*(1-z)))+((16 : ℝ)*(z^2))))))+(((t^3)*((1-t)*(((44 : ℝ)*((1-z)^2))+(((65 : ℝ)*(z*(1-z)))+((27 : ℝ)*(z^2))))))+((t^4)*(((6 : ℝ)*(z*(1-z)))+((6 : ℝ)*(z^2)))))))

theorem upperCertificate00Block03_identity (t z : ℝ) :
    upperCertificate00Block03 t z=(((((-1 : ℝ)*((t^4)*z))+(((-4 : ℝ)*(t^4))+((-3 : ℝ)*((t^3)*(z^2)))))+((((18 : ℝ)*((t^3)*z))+((-20 : ℝ)*(t^3)))+(((1 : ℝ)*((t^2)*(z^2)))+((6 : ℝ)*((t^2)*z)))))+((((9 : ℝ)*(t^2))+(((1 : ℝ)*(t*(z^2)))+((-15 : ℝ)*(t*z))))+((((14 : ℝ)*t)+((1 : ℝ)*(z^2)))+(((-2 : ℝ)*z)+(1 : ℝ))))) := by
  have hz0 : ((1 : ℝ)*((1-z)^2)) = (((1 : ℝ)*(z^2))+(((-2 : ℝ)*z)+(1 : ℝ))) := by ring
  have hz1 : (((18 : ℝ)*((1-z)^2))+((13 : ℝ)*(z*(1-z)))) = (((5 : ℝ)*(z^2))+(((-23 : ℝ)*z)+(18 : ℝ))) := by ring
  have hz2 : (((57 : ℝ)*((1-z)^2))+(((63 : ℝ)*(z*(1-z)))+((16 : ℝ)*(z^2)))) = (((10 : ℝ)*(z^2))+(((-51 : ℝ)*z)+(57 : ℝ))) := by ring
  have hz3 : (((44 : ℝ)*((1-z)^2))+(((65 : ℝ)*(z*(1-z)))+((27 : ℝ)*(z^2)))) = (((6 : ℝ)*(z^2))+(((-23 : ℝ)*z)+(44 : ℝ))) := by ring
  have hz4 : (((6 : ℝ)*(z*(1-z)))+((6 : ℝ)*(z^2))) = ((6 : ℝ)*z) := by ring
  unfold upperCertificate00Block03
  simp only [hz0,hz1,hz2,hz3,hz4]
  ring

theorem upperCertificate00Block03_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate00Block03 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate00Block03
  positivity

def upperCertificate00Block04 (t z : ℝ) : ℝ := (((((1-t)^4)*((5 : ℝ)*((1-z)^2)))+(t*(((1-t)^3)*(((39 : ℝ)*((1-z)^2))+((16 : ℝ)*(z*(1-z)))))))+(((t^2)*(((1-t)^2)*(((75 : ℝ)*((1-z)^2))+(((47 : ℝ)*(z*(1-z)))+((8 : ℝ)*(z^2))))))+(((t^3)*((1-t)*(((41 : ℝ)*((1-z)^2))+(((35 : ℝ)*(z*(1-z)))+((10 : ℝ)*(z^2))))))+((t^4)*(((2 : ℝ)*(z*(1-z)))+((2 : ℝ)*(z^2)))))))

theorem upperCertificate00Block04_identity (t z : ℝ) :
    upperCertificate00Block04 t z=(((((2 : ℝ)*((t^4)*(z^2)))+(((-2 : ℝ)*((t^4)*z))+((-7 : ℝ)*((t^3)*(z^2)))))+((((13 : ℝ)*((t^3)*z))+((-12 : ℝ)*(t^3)))+(((-3 : ℝ)*((t^2)*(z^2)))+((23 : ℝ)*((t^2)*z)))))+((((-12 : ℝ)*(t^2))+(((3 : ℝ)*(t*(z^2)))+((-22 : ℝ)*(t*z))))+((((19 : ℝ)*t)+((5 : ℝ)*(z^2)))+(((-10 : ℝ)*z)+(5 : ℝ))))) := by
  have hz0 : ((5 : ℝ)*((1-z)^2)) = (((5 : ℝ)*(z^2))+(((-10 : ℝ)*z)+(5 : ℝ))) := by ring
  have hz1 : (((39 : ℝ)*((1-z)^2))+((16 : ℝ)*(z*(1-z)))) = (((23 : ℝ)*(z^2))+(((-62 : ℝ)*z)+(39 : ℝ))) := by ring
  have hz2 : (((75 : ℝ)*((1-z)^2))+(((47 : ℝ)*(z*(1-z)))+((8 : ℝ)*(z^2)))) = (((36 : ℝ)*(z^2))+(((-103 : ℝ)*z)+(75 : ℝ))) := by ring
  have hz3 : (((41 : ℝ)*((1-z)^2))+(((35 : ℝ)*(z*(1-z)))+((10 : ℝ)*(z^2)))) = (((16 : ℝ)*(z^2))+(((-47 : ℝ)*z)+(41 : ℝ))) := by ring
  have hz4 : (((2 : ℝ)*(z*(1-z)))+((2 : ℝ)*(z^2))) = ((2 : ℝ)*z) := by ring
  unfold upperCertificate00Block04
  simp only [hz0,hz1,hz2,hz3,hz4]
  ring

theorem upperCertificate00Block04_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate00Block04 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate00Block04
  positivity

def upperCertificate00Block05 (t z : ℝ) : ℝ := (((((1-t)^4)*((8 : ℝ)*((1-z)^2)))+(t*(((1-t)^3)*(((36 : ℝ)*((1-z)^2))+((4 : ℝ)*(z*(1-z)))))))+(((t^2)*(((1-t)^2)*(((48 : ℝ)*((1-z)^2))+((10 : ℝ)*(z*(1-z))))))+((t^3)*((1-t)*(((20 : ℝ)*((1-z)^2))+((6 : ℝ)*(z*(1-z))))))))

theorem upperCertificate00Block05_identity (t z : ℝ) :
    upperCertificate00Block05 t z=(((((2 : ℝ)*((t^3)*(z^2)))+((-2 : ℝ)*((t^3)*z)))+(((-10 : ℝ)*((t^2)*(z^2)))+(((22 : ℝ)*((t^2)*z))+((-12 : ℝ)*(t^2)))))+((((-4 : ℝ)*(t*z))+((4 : ℝ)*t))+(((8 : ℝ)*(z^2))+(((-16 : ℝ)*z)+(8 : ℝ))))) := by
  have hz0 : ((8 : ℝ)*((1-z)^2)) = (((8 : ℝ)*(z^2))+(((-16 : ℝ)*z)+(8 : ℝ))) := by ring
  have hz1 : (((36 : ℝ)*((1-z)^2))+((4 : ℝ)*(z*(1-z)))) = (((32 : ℝ)*(z^2))+(((-68 : ℝ)*z)+(36 : ℝ))) := by ring
  have hz2 : (((48 : ℝ)*((1-z)^2))+((10 : ℝ)*(z*(1-z)))) = (((38 : ℝ)*(z^2))+(((-86 : ℝ)*z)+(48 : ℝ))) := by ring
  have hz3 : (((20 : ℝ)*((1-z)^2))+((6 : ℝ)*(z*(1-z)))) = (((14 : ℝ)*(z^2))+(((-34 : ℝ)*z)+(20 : ℝ))) := by ring
  unfold upperCertificate00Block05
  simp only [hz0,hz1,hz2,hz3]
  ring

theorem upperCertificate00Block05_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate00Block05 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate00Block05
  positivity

def upperCertificate00Block06 (t z : ℝ) : ℝ := (((((1-t)^4)*((4 : ℝ)*((1-z)^2)))+(t*(((1-t)^3)*((12 : ℝ)*((1-z)^2)))))+(((t^2)*(((1-t)^2)*((12 : ℝ)*((1-z)^2))))+((t^3)*((1-t)*((4 : ℝ)*((1-z)^2))))))

theorem upperCertificate00Block06_identity (t z : ℝ) :
    upperCertificate00Block06 t z=((((-4 : ℝ)*(t*(z^2)))+(((8 : ℝ)*(t*z))+((-4 : ℝ)*t)))+(((4 : ℝ)*(z^2))+(((-8 : ℝ)*z)+(4 : ℝ)))) := by
  have hz0 : ((4 : ℝ)*((1-z)^2)) = (((4 : ℝ)*(z^2))+(((-8 : ℝ)*z)+(4 : ℝ))) := by ring
  have hz1 : ((12 : ℝ)*((1-z)^2)) = (((12 : ℝ)*(z^2))+(((-24 : ℝ)*z)+(12 : ℝ))) := by ring
  have hz2 : ((12 : ℝ)*((1-z)^2)) = (((12 : ℝ)*(z^2))+(((-24 : ℝ)*z)+(12 : ℝ))) := by ring
  have hz3 : ((4 : ℝ)*((1-z)^2)) = (((4 : ℝ)*(z^2))+(((-8 : ℝ)*z)+(4 : ℝ))) := by ring
  unfold upperCertificate00Block06
  simp only [hz0,hz1,hz2,hz3]
  ring

theorem upperCertificate00Block06_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate00Block06 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate00Block06
  positivity

def upperCertificate00 (a t z : ℝ) : ℝ := (((((1-a)^6)*(upperCertificate00Block00 t z))+((a*(((1-a)^5)*(upperCertificate00Block01 t z)))+((a^2)*(((1-a)^4)*(upperCertificate00Block02 t z)))))+((((a^3)*(((1-a)^3)*(upperCertificate00Block03 t z)))+((a^4)*(((1-a)^2)*(upperCertificate00Block04 t z))))+(((a^5)*((1-a)*(upperCertificate00Block05 t z)))+((a^6)*(upperCertificate00Block06 t z)))))

theorem upperCertificate00_identity (a t z : ℝ) :
    upperAtom00 a t z=upperCertificate00 a t z := by
  unfold upperCertificate00
  rw [upperCertificate00Block00_identity,upperCertificate00Block01_identity,upperCertificate00Block02_identity,upperCertificate00Block03_identity,upperCertificate00Block04_identity,upperCertificate00Block05_identity,upperCertificate00Block06_identity]
  unfold upperAtom00 
  ring

theorem upperAtom00_pos {a t z : ℝ} (ha : 0<a) (hau : a<1)
    (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) : 0<upperAtom00 a t z := by
  rw [upperCertificate00_identity]
  have hac : 0<1-a := by linarith
  have hb0 := upperCertificate00Block00_pos ht htu hz hzu
  have hb1 := upperCertificate00Block01_pos ht htu hz hzu
  have hb2 := upperCertificate00Block02_pos ht htu hz hzu
  have hb3 := upperCertificate00Block03_pos ht htu hz hzu
  have hb4 := upperCertificate00Block04_pos ht htu hz hzu
  have hb5 := upperCertificate00Block05_pos ht htu hz hzu
  have hb6 := upperCertificate00Block06_pos ht htu hz hzu
  unfold upperCertificate00
  positivity

theorem upperNum00_pos {a f rho : ℝ} (ha : 0<a) (hau : a<1)
    (haf : a<f) (hf : f<1) (hr : 0<rho) (hru : rho<1) : 0<upperNum00 a f rho := by
  obtain ⟨ht,htu,hfeq⟩ := upper_cube_coordinate hau haf hf
  have hac : 0<1-a := by linarith
  have hp := upperAtom00_pos ha hau ht htu hr hru
  have he := upperNum00_map a ((f-a)/(1-a)) rho
  rw [hfeq] at he
  rw [he]
  exact mul_pos (pow_pos hac _) hp

end LeanVerification.PositiveDCompletion
