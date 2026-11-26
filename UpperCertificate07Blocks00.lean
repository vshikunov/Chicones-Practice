import LeanVerification.PositiveDCompletion.UpperCertificate07Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperCertificate07Block00_identity (t z : ℝ) :
    upperCertificate07Block00 t z=(((upperCertificate07Block00Coeff0 t)*z^(0 : ℕ)+((upperCertificate07Block00Coeff1 t)*z^(1 : ℕ)+(upperCertificate07Block00Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate07Block00Coeff3 t)*z^(3 : ℕ)+(upperCertificate07Block00Coeff4 t)*z^(4 : ℕ))+((upperCertificate07Block00Coeff5 t)*z^(5 : ℕ)+(upperCertificate07Block00Coeff6 t)*z^(6 : ℕ)))) := by
  have hz8 : ((((84 : ℝ)*((1-z)^(6 : ℕ)))+(((504 : ℝ)*(z*((1-z)^(5 : ℕ))))+((1260 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((1680 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((1260 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((504 : ℝ)*((z^(5 : ℕ))*(1-z)))+((84 : ℝ)*(z^(6 : ℕ))))))=(84 : ℝ) := by ring
  have hz9 : ((((168 : ℝ)*((1-z)^(6 : ℕ)))+(((1008 : ℝ)*(z*((1-z)^(5 : ℕ))))+((2520 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((3360 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((2520 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((1008 : ℝ)*((z^(5 : ℕ))*(1-z)))+((168 : ℝ)*(z^(6 : ℕ))))))=(168 : ℝ) := by ring
  have hz10 : ((((84 : ℝ)*((1-z)^(6 : ℕ)))+(((504 : ℝ)*(z*((1-z)^(5 : ℕ))))+((1260 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((1680 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((1260 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((504 : ℝ)*((z^(5 : ℕ))*(1-z)))+((84 : ℝ)*(z^(6 : ℕ))))))=(84 : ℝ) := by ring
  unfold upperCertificate07Block00
  simp only [hz8,hz9,hz10]
  unfold upperCertificate07Block00Coeff0 upperCertificate07Block00Coeff1 upperCertificate07Block00Coeff2 upperCertificate07Block00Coeff3 upperCertificate07Block00Coeff4 upperCertificate07Block00Coeff5 upperCertificate07Block00Coeff6
  ring

theorem upperCertificate07Block00_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate07Block00 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate07Block00
  positivity

theorem upperCertificate07Block01_identity (t z : ℝ) :
    upperCertificate07Block01 t z=(((upperCertificate07Block01Coeff0 t)*z^(0 : ℕ)+((upperCertificate07Block01Coeff1 t)*z^(1 : ℕ)+(upperCertificate07Block01Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate07Block01Coeff3 t)*z^(3 : ℕ)+(upperCertificate07Block01Coeff4 t)*z^(4 : ℕ))+((upperCertificate07Block01Coeff5 t)*z^(5 : ℕ)+(upperCertificate07Block01Coeff6 t)*z^(6 : ℕ)))) := by
  have hz7 : ((((672 : ℝ)*((1-z)^(6 : ℕ)))+(((3900 : ℝ)*(z*((1-z)^(5 : ℕ))))+((9420 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((12120 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((8760 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((3372 : ℝ)*((z^(5 : ℕ))*(1-z)))+((540 : ℝ)*(z^(6 : ℕ))))))=(((-132 : ℝ)*z)+(672 : ℝ)) := by ring
  have hz8 : ((((3546 : ℝ)*((1-z)^(6 : ℕ)))+(((21072 : ℝ)*(z*((1-z)^(5 : ℕ))))+((52170 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((68880 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((51150 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((20256 : ℝ)*((z^(5 : ℕ))*(1-z)))+((3342 : ℝ)*(z^(6 : ℕ))))))=(((-204 : ℝ)*z)+(3546 : ℝ)) := by ring
  have hz9 : ((((4794 : ℝ)*((1-z)^(6 : ℕ)))+(((28944 : ℝ)*(z*((1-z)^(5 : ℕ))))+((72810 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((97680 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((73710 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((29664 : ℝ)*((z^(5 : ℕ))*(1-z)))+((4974 : ℝ)*(z^(6 : ℕ))))))=(((180 : ℝ)*z)+(4794 : ℝ)) := by ring
  have hz10 : ((((1920 : ℝ)*((1-z)^(6 : ℕ)))+(((11964 : ℝ)*(z*((1-z)^(5 : ℕ))))+((31020 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((42840 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((33240 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((13740 : ℝ)*((z^(5 : ℕ))*(1-z)))+((2364 : ℝ)*(z^(6 : ℕ))))))=(((444 : ℝ)*z)+(1920 : ℝ)) := by ring
  have hz11 : ((((192 : ℝ)*(z*((1-z)^(5 : ℕ))))+(((960 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))+((1920 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))))+(((1920 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ))))+(((960 : ℝ)*((z^(5 : ℕ))*(1-z)))+((192 : ℝ)*(z^(6 : ℕ))))))=((192 : ℝ)*z) := by ring
  unfold upperCertificate07Block01
  simp only [hz7,hz8,hz9,hz10,hz11]
  unfold upperCertificate07Block01Coeff0 upperCertificate07Block01Coeff1 upperCertificate07Block01Coeff2 upperCertificate07Block01Coeff3 upperCertificate07Block01Coeff4 upperCertificate07Block01Coeff5 upperCertificate07Block01Coeff6
  ring

theorem upperCertificate07Block01_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate07Block01 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate07Block01
  positivity

theorem upperCertificate07Block02_identity (t z : ℝ) :
    upperCertificate07Block02 t z=(((upperCertificate07Block02Coeff0 t)*z^(0 : ℕ)+((upperCertificate07Block02Coeff1 t)*z^(1 : ℕ)+(upperCertificate07Block02Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate07Block02Coeff3 t)*z^(3 : ℕ)+(upperCertificate07Block02Coeff4 t)*z^(4 : ℕ))+((upperCertificate07Block02Coeff5 t)*z^(5 : ℕ)+(upperCertificate07Block02Coeff6 t)*z^(6 : ℕ)))) := by
  have hz6 : ((((2352 : ℝ)*((1-z)^(6 : ℕ)))+(((12924 : ℝ)*(z*((1-z)^(5 : ℕ))))+((29388 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((35352 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((23688 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((8364 : ℝ)*((z^(5 : ℕ))*(1-z)))+((1212 : ℝ)*(z^(6 : ℕ))))))=(((48 : ℝ)*(z^(2 : ℕ)))+(((-1188 : ℝ)*z)+(2352 : ℝ))) := by ring
  have hz7 : ((((21648 : ℝ)*((1-z)^(6 : ℕ)))+(((123482 : ℝ)*(z*((1-z)^(5 : ℕ))))+((292786 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((369284 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((261236 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((98242 : ℝ)*((z^(5 : ℕ))*(1-z)))+((15338 : ℝ)*(z^(6 : ℕ))))))=(((96 : ℝ)*(z^(2 : ℕ)))+(((-6406 : ℝ)*z)+(21648 : ℝ))) := by ring
  have hz8 : ((((61122 : ℝ)*((1-z)^(6 : ℕ)))+(((359236 : ℝ)*(z*((1-z)^(5 : ℕ))))+((879254 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((1147096 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((841294 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((328868 : ℝ)*((z^(5 : ℕ))*(1-z)))+((53530 : ℝ)*(z^(6 : ℕ))))))=(((-96 : ℝ)*(z^(2 : ℕ)))+(((-7496 : ℝ)*z)+(61122 : ℝ))) := by ring
  have hz9 : ((((62268 : ℝ)*((1-z)^(6 : ℕ)))+(((376458 : ℝ)*(z*((1-z)^(5 : ℕ))))+((947886 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((1272324 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((960216 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((386322 : ℝ)*((z^(5 : ℕ))*(1-z)))+((64734 : ℝ)*(z^(6 : ℕ))))))=(((-384 : ℝ)*(z^(2 : ℕ)))+(((2850 : ℝ)*z)+(62268 : ℝ))) := by ring
  have hz10 : ((((20688 : ℝ)*((1-z)^(6 : ℕ)))+(((132632 : ℝ)*(z*((1-z)^(5 : ℕ))))+((352504 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((497456 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((393344 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((165304 : ℝ)*((z^(5 : ℕ))*(1-z)))+((28856 : ℝ)*(z^(6 : ℕ))))))=(((-336 : ℝ)*(z^(2 : ℕ)))+(((8504 : ℝ)*z)+(20688 : ℝ))) := by ring
  have hz11 : ((((3376 : ℝ)*(z*((1-z)^(5 : ℕ))))+(((16784 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))+((33376 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))))+(((33184 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ))))+(((16496 : ℝ)*((z^(5 : ℕ))*(1-z)))+((3280 : ℝ)*(z^(6 : ℕ))))))=(((-96 : ℝ)*(z^(2 : ℕ)))+((3376 : ℝ)*z)) := by ring
  unfold upperCertificate07Block02
  simp only [hz6,hz7,hz8,hz9,hz10,hz11]
  unfold upperCertificate07Block02Coeff0 upperCertificate07Block02Coeff1 upperCertificate07Block02Coeff2 upperCertificate07Block02Coeff3 upperCertificate07Block02Coeff4 upperCertificate07Block02Coeff5 upperCertificate07Block02Coeff6
  ring

theorem upperCertificate07Block02_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate07Block02 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate07Block02
  positivity

theorem upperCertificate07Block03_identity (t z : ℝ) :
    upperCertificate07Block03 t z=(((upperCertificate07Block03Coeff0 t)*z^(0 : ℕ)+((upperCertificate07Block03Coeff1 t)*z^(1 : ℕ)+(upperCertificate07Block03Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate07Block03Coeff3 t)*z^(3 : ℕ)+(upperCertificate07Block03Coeff4 t)*z^(4 : ℕ))+((upperCertificate07Block03Coeff5 t)*z^(5 : ℕ)+(upperCertificate07Block03Coeff6 t)*z^(6 : ℕ)))) := by
  have hz5 : ((((4704 : ℝ)*((1-z)^(6 : ℕ)))+(((23868 : ℝ)*(z*((1-z)^(5 : ℕ))))+((49488 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((53352 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((31248 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((9276 : ℝ)*((z^(5 : ℕ))*(1-z)))+((1056 : ℝ)*(z^(6 : ℕ))))))=(((708 : ℝ)*(z^(2 : ℕ)))+(((-4356 : ℝ)*z)+(4704 : ℝ))) := by ring
  have hz6 : ((((66360 : ℝ)*((1-z)^(6 : ℕ)))+(((355156 : ℝ)*(z*((1-z)^(5 : ℕ))))+((784570 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((913920 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((590500 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((199900 : ℝ)*((z^(5 : ℕ))*(1-z)))+((27546 : ℝ)*(z^(6 : ℕ))))))=(((4190 : ℝ)*(z^(2 : ℕ)))+(((-43004 : ℝ)*z)+(66360 : ℝ))) := by ring
  have hz7 : ((((310872 : ℝ)*((1-z)^(6 : ℕ)))+(((1735085 : ℝ)*(z*((1-z)^(5 : ℕ))))+((4019359 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((4944026 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((3403694 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((1242553 : ℝ)*((z^(5 : ℕ))*(1-z)))+((187739 : ℝ)*(z^(6 : ℕ))))))=(((7014 : ℝ)*(z^(2 : ℕ)))+(((-130147 : ℝ)*z)+(310872 : ℝ))) := by ring
  have hz8 : ((((607080 : ℝ)*((1-z)^(6 : ℕ)))+(((3511709 : ℝ)*(z*((1-z)^(5 : ℕ))))+((8453039 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((10836666 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((7802654 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((2991401 : ℝ)*((z^(5 : ℕ))*(1-z)))+((477003 : ℝ)*(z^(6 : ℕ))))))=(((694 : ℝ)*(z^(2 : ℕ)))+(((-130771 : ℝ)*z)+(607080 : ℝ))) := by ring
  have hz9 : ((((494310 : ℝ)*((1-z)^(6 : ℕ)))+(((2971024 : ℝ)*(z*((1-z)^(5 : ℕ))))+((7431748 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((9902952 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((7413958 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((2956792 : ℝ)*((z^(5 : ℕ))*(1-z)))+((490752 : ℝ)*(z^(6 : ℕ))))))=(((-8722 : ℝ)*(z^(2 : ℕ)))+(((5164 : ℝ)*z)+(494310 : ℝ))) := by ring
  have hz10 : ((((139704 : ℝ)*((1-z)^(6 : ℕ)))+(((910388 : ℝ)*(z*((1-z)^(5 : ℕ))))+((2448208 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((3483032 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((2768168 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((1166356 : ℝ)*((z^(5 : ℕ))*(1-z)))+((203696 : ℝ)*(z^(6 : ℕ))))))=(((-8172 : ℝ)*(z^(2 : ℕ)))+(((72164 : ℝ)*z)+(139704 : ℝ))) := by ring
  have hz11 : ((((27728 : ℝ)*(z*((1-z)^(5 : ℕ))))+(((136352 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))+((268128 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))))+(((263552 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ))))+(((129488 : ℝ)*((z^(5 : ℕ))*(1-z)))+((25440 : ℝ)*(z^(6 : ℕ))))))=(((-2288 : ℝ)*(z^(2 : ℕ)))+((27728 : ℝ)*z)) := by ring
  unfold upperCertificate07Block03
  simp only [hz5,hz6,hz7,hz8,hz9,hz10,hz11]
  unfold upperCertificate07Block03Coeff0 upperCertificate07Block03Coeff1 upperCertificate07Block03Coeff2 upperCertificate07Block03Coeff3 upperCertificate07Block03Coeff4 upperCertificate07Block03Coeff5 upperCertificate07Block03Coeff6
  ring

theorem upperCertificate07Block03_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate07Block03 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate07Block03
  positivity

theorem upperCertificate07Block04_identity (t z : ℝ) :
    upperCertificate07Block04 t z=(((upperCertificate07Block04Coeff0 t)*z^(0 : ℕ)+((upperCertificate07Block04Coeff1 t)*z^(1 : ℕ)+(upperCertificate07Block04Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate07Block04Coeff3 t)*z^(3 : ℕ)+(upperCertificate07Block04Coeff4 t)*z^(4 : ℕ))+((upperCertificate07Block04Coeff5 t)*z^(5 : ℕ)+(upperCertificate07Block04Coeff6 t)*z^(6 : ℕ)))) := by
  have hz4 : ((((5880 : ℝ)*((1-z)^(6 : ℕ)))+(((26700 : ℝ)*(z*((1-z)^(5 : ℕ))))+((48396 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((44028 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((20508 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((4296 : ℝ)*((z^(5 : ℕ))*(1-z)))+((240 : ℝ)*(z^(6 : ℕ))))))=((((-156 : ℝ)*(z^(3 : ℕ)))+((3096 : ℝ)*(z^(2 : ℕ))))+(((-8580 : ℝ)*z)+(5880 : ℝ))) := by ring
  have hz5 : ((((120960 : ℝ)*((1-z)^(6 : ℕ)))+(((592422 : ℝ)*(z*((1-z)^(5 : ℕ))))+((1180862 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((1217446 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((676986 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((188732 : ℝ)*((z^(5 : ℕ))*(1-z)))+((19792 : ℝ)*(z^(6 : ℕ))))))=((((-982 : ℝ)*(z^(3 : ℕ)))+((33152 : ℝ)*(z^(2 : ℕ))))+(((-133338 : ℝ)*z)+(120960 : ℝ))) := by ring
  have hz6 : ((((852096 : ℝ)*((1-z)^(6 : ℕ)))+(((4418593 : ℝ)*(z*((1-z)^(5 : ℕ))))+((9430604 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((10576110 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((6549196 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((2112089 : ℝ)*((z^(5 : ℕ))*(1-z)))+((274896 : ℝ)*(z^(6 : ℕ))))))=((((-2296 : ℝ)*(z^(3 : ℕ)))+((119079 : ℝ)*(z^(2 : ℕ))))+(((-693983 : ℝ)*z)+(852096 : ℝ))) := by ring
  have hz7 : ((((2680896 : ℝ)*((1-z)^(6 : ℕ)))+(((14555292 : ℝ)*(z*((1-z)^(5 : ℕ))))+((32738848 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((39018164 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((25960884 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((9131584 : ℝ)*((z^(5 : ℕ))*(1-z)))+((1324412 : ℝ)*(z^(6 : ℕ))))))=((((-2228 : ℝ)*(z^(3 : ℕ)))+((175828 : ℝ)*(z^(2 : ℕ))))+(((-1530084 : ℝ)*z)+(2680896 : ℝ))) := by ring
  have hz8 : ((((4005720 : ℝ)*((1-z)^(6 : ℕ)))+(((22652234 : ℝ)*(z*((1-z)^(5 : ℕ))))+((53249485 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((66589868 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((46709234 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((17419954 : ℝ)*((z^(5 : ℕ))*(1-z)))+((2697617 : ℝ)*(z^(6 : ℕ))))))=((((-132 : ℝ)*(z^(3 : ℕ)))+((74115 : ℝ)*(z^(2 : ℕ))))+(((-1382086 : ℝ)*z)+(4005720 : ℝ))) := by ring
  have hz9 : ((((2705856 : ℝ)*((1-z)^(6 : ℕ)))+(((16027192 : ℝ)*(z*((1-z)^(5 : ℕ))))+((39474758 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((51745698 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((38072626 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((14906366 : ℝ)*((z^(5 : ℕ))*(1-z)))+((2426016 : ℝ)*(z^(6 : ℕ))))))=((((1466 : ℝ)*(z^(3 : ℕ)))+((-73362 : ℝ)*(z^(2 : ℕ))))+(((-207944 : ℝ)*z)+(2705856 : ℝ))) := by ring
  have hz10 : ((((662976 : ℝ)*((1-z)^(6 : ℕ)))+(((4332432 : ℝ)*(z*((1-z)^(5 : ℕ))))+((11633608 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((16470728 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((12990216 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((5418376 : ℝ)*((z^(5 : ℕ))*(1-z)))+((934736 : ℝ)*(z^(6 : ℕ))))))=((((1096 : ℝ)*(z^(3 : ℕ)))+((-83912 : ℝ)*(z^(2 : ℕ))))+(((354576 : ℝ)*z)+(662976 : ℝ))) := by ring
  have hz11 : ((((141248 : ℝ)*(z*((1-z)^(5 : ℕ))))+(((683000 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))+((1319776 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))))+(((1273808 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ))))+(((614048 : ℝ)*((z^(5 : ℕ))*(1-z)))+((118264 : ℝ)*(z^(6 : ℕ))))))=(((256 : ℝ)*(z^(3 : ℕ)))+(((-23240 : ℝ)*(z^(2 : ℕ)))+((141248 : ℝ)*z))) := by ring
  unfold upperCertificate07Block04
  simp only [hz4,hz5,hz6,hz7,hz8,hz9,hz10,hz11]
  unfold upperCertificate07Block04Coeff0 upperCertificate07Block04Coeff1 upperCertificate07Block04Coeff2 upperCertificate07Block04Coeff3 upperCertificate07Block04Coeff4 upperCertificate07Block04Coeff5 upperCertificate07Block04Coeff6
  ring

theorem upperCertificate07Block04_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate07Block04 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate07Block04
  positivity

end LeanVerification.PositiveDCompletion
