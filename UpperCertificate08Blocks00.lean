import LeanVerification.PositiveDCompletion.UpperCertificate08Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperCertificate08Block00_identity (t z : ℝ) :
    upperCertificate08Block00 t z=(((upperCertificate08Block00Coeff0 t)*z^(0 : ℕ)+((upperCertificate08Block00Coeff1 t)*z^(1 : ℕ)+(upperCertificate08Block00Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate08Block00Coeff3 t)*z^(3 : ℕ)+(upperCertificate08Block00Coeff4 t)*z^(4 : ℕ))+((upperCertificate08Block00Coeff5 t)*z^(5 : ℕ)+(upperCertificate08Block00Coeff6 t)*z^(6 : ℕ)))) := by
  have hz15 : ((((32 : ℝ)*((1-z)^(6 : ℕ)))+(((192 : ℝ)*(z*((1-z)^(5 : ℕ))))+((480 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((640 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((480 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((192 : ℝ)*((z^(5 : ℕ))*(1-z)))+((32 : ℝ)*(z^(6 : ℕ))))))=(32 : ℝ) := by ring
  have hz16 : ((((64 : ℝ)*((1-z)^(6 : ℕ)))+(((384 : ℝ)*(z*((1-z)^(5 : ℕ))))+((960 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((1280 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((960 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((384 : ℝ)*((z^(5 : ℕ))*(1-z)))+((64 : ℝ)*(z^(6 : ℕ))))))=(64 : ℝ) := by ring
  have hz17 : ((((32 : ℝ)*((1-z)^(6 : ℕ)))+(((192 : ℝ)*(z*((1-z)^(5 : ℕ))))+((480 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((640 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((480 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((192 : ℝ)*((z^(5 : ℕ))*(1-z)))+((32 : ℝ)*(z^(6 : ℕ))))))=(32 : ℝ) := by ring
  unfold upperCertificate08Block00
  simp only [hz15,hz16,hz17]
  unfold upperCertificate08Block00Coeff0 upperCertificate08Block00Coeff1 upperCertificate08Block00Coeff2 upperCertificate08Block00Coeff3 upperCertificate08Block00Coeff4 upperCertificate08Block00Coeff5 upperCertificate08Block00Coeff6
  ring

theorem upperCertificate08Block00_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate08Block00 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate08Block00
  positivity

theorem upperCertificate08Block01_identity (t z : ℝ) :
    upperCertificate08Block01 t z=(((upperCertificate08Block01Coeff0 t)*z^(0 : ℕ)+((upperCertificate08Block01Coeff1 t)*z^(1 : ℕ)+(upperCertificate08Block01Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate08Block01Coeff3 t)*z^(3 : ℕ)+(upperCertificate08Block01Coeff4 t)*z^(4 : ℕ))+((upperCertificate08Block01Coeff5 t)*z^(5 : ℕ)+(upperCertificate08Block01Coeff6 t)*z^(6 : ℕ)))) := by
  have hz14 : ((((480 : ℝ)*((1-z)^(6 : ℕ)))+(((2880 : ℝ)*(z*((1-z)^(5 : ℕ))))+((7200 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((9600 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((7200 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((2880 : ℝ)*((z^(5 : ℕ))*(1-z)))+((480 : ℝ)*(z^(6 : ℕ))))))=(480 : ℝ) := by ring
  have hz15 : ((((2042 : ℝ)*((1-z)^(6 : ℕ)))+(((12252 : ℝ)*(z*((1-z)^(5 : ℕ))))+((30630 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((40840 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((30630 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((12252 : ℝ)*((z^(5 : ℕ))*(1-z)))+((2042 : ℝ)*(z^(6 : ℕ))))))=(2042 : ℝ) := by ring
  have hz16 : ((((2530 : ℝ)*((1-z)^(6 : ℕ)))+(((15180 : ℝ)*(z*((1-z)^(5 : ℕ))))+((37950 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((50600 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((37950 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((15180 : ℝ)*((z^(5 : ℕ))*(1-z)))+((2530 : ℝ)*(z^(6 : ℕ))))))=(2530 : ℝ) := by ring
  have hz17 : ((((968 : ℝ)*((1-z)^(6 : ℕ)))+(((5808 : ℝ)*(z*((1-z)^(5 : ℕ))))+((14520 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((19360 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((14520 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((5808 : ℝ)*((z^(5 : ℕ))*(1-z)))+((968 : ℝ)*(z^(6 : ℕ))))))=(968 : ℝ) := by ring
  unfold upperCertificate08Block01
  simp only [hz14,hz15,hz16,hz17]
  unfold upperCertificate08Block01Coeff0 upperCertificate08Block01Coeff1 upperCertificate08Block01Coeff2 upperCertificate08Block01Coeff3 upperCertificate08Block01Coeff4 upperCertificate08Block01Coeff5 upperCertificate08Block01Coeff6
  ring

theorem upperCertificate08Block01_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate08Block01 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate08Block01
  positivity

theorem upperCertificate08Block02_identity (t z : ℝ) :
    upperCertificate08Block02 t z=(((upperCertificate08Block02Coeff0 t)*z^(0 : ℕ)+((upperCertificate08Block02Coeff1 t)*z^(1 : ℕ)+(upperCertificate08Block02Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate08Block02Coeff3 t)*z^(3 : ℕ)+(upperCertificate08Block02Coeff4 t)*z^(4 : ℕ))+((upperCertificate08Block02Coeff5 t)*z^(5 : ℕ)+(upperCertificate08Block02Coeff6 t)*z^(6 : ℕ)))) := by
  have hz13 : ((((3360 : ℝ)*((1-z)^(6 : ℕ)))+(((20096 : ℝ)*(z*((1-z)^(5 : ℕ))))+((50080 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((66560 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((49760 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((19840 : ℝ)*((z^(5 : ℕ))*(1-z)))+((3296 : ℝ)*(z^(6 : ℕ))))))=(((-64 : ℝ)*z)+(3360 : ℝ)) := by ring
  have hz14 : ((((22470 : ℝ)*((1-z)^(6 : ℕ)))+(((134652 : ℝ)*(z*((1-z)^(5 : ℕ))))+((336210 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((447720 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((335370 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((133980 : ℝ)*((z^(5 : ℕ))*(1-z)))+((22302 : ℝ)*(z^(6 : ℕ))))))=(((-168 : ℝ)*z)+(22470 : ℝ)) := by ring
  have hz15 : ((((50651 : ℝ)*((1-z)^(6 : ℕ)))+(((303874 : ℝ)*(z*((1-z)^(5 : ℕ))))+((759605 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((1012700 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((759445 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((303746 : ℝ)*((z^(5 : ℕ))*(1-z)))+((50619 : ℝ)*(z^(6 : ℕ))))))=(((-32 : ℝ)*z)+(50651 : ℝ)) := by ring
  have hz16 : ((((45468 : ℝ)*((1-z)^(6 : ℕ)))+(((273080 : ℝ)*(z*((1-z)^(5 : ℕ))))+((683380 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((912080 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((684740 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((274168 : ℝ)*((z^(5 : ℕ))*(1-z)))+((45740 : ℝ)*(z^(6 : ℕ))))))=(((272 : ℝ)*z)+(45468 : ℝ)) := by ring
  have hz17 : ((((14036 : ℝ)*((1-z)^(6 : ℕ)))+(((84504 : ℝ)*(z*((1-z)^(5 : ℕ))))+((211980 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((283600 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((213420 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((85656 : ℝ)*((z^(5 : ℕ))*(1-z)))+((14324 : ℝ)*(z^(6 : ℕ))))))=(((288 : ℝ)*z)+(14036 : ℝ)) := by ring
  have hz18 : ((((88 : ℝ)*(z*((1-z)^(5 : ℕ))))+(((440 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))+((880 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))))+(((880 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ))))+(((440 : ℝ)*((z^(5 : ℕ))*(1-z)))+((88 : ℝ)*(z^(6 : ℕ))))))=((88 : ℝ)*z) := by ring
  unfold upperCertificate08Block02
  simp only [hz13,hz14,hz15,hz16,hz17,hz18]
  unfold upperCertificate08Block02Coeff0 upperCertificate08Block02Coeff1 upperCertificate08Block02Coeff2 upperCertificate08Block02Coeff3 upperCertificate08Block02Coeff4 upperCertificate08Block02Coeff5 upperCertificate08Block02Coeff6
  ring

theorem upperCertificate08Block02_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate08Block02 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate08Block02
  positivity

theorem upperCertificate08Block03_identity (t z : ℝ) :
    upperCertificate08Block03 t z=(((upperCertificate08Block03Coeff0 t)*z^(0 : ℕ)+((upperCertificate08Block03Coeff1 t)*z^(1 : ℕ)+(upperCertificate08Block03Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate08Block03Coeff3 t)*z^(3 : ℕ)+(upperCertificate08Block03Coeff4 t)*z^(4 : ℕ))+((upperCertificate08Block03Coeff5 t)*z^(5 : ℕ)+(upperCertificate08Block03Coeff6 t)*z^(6 : ℕ)))) := by
  have hz12 : ((((14560 : ℝ)*((1-z)^(6 : ℕ)))+(((86424 : ℝ)*(z*((1-z)^(5 : ℕ))))+((213720 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((281840 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((209040 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((82680 : ℝ)*((z^(5 : ℕ))*(1-z)))+((13624 : ℝ)*(z^(6 : ℕ))))))=(((-936 : ℝ)*z)+(14560 : ℝ)) := by ring
  have hz13 : ((((136010 : ℝ)*((1-z)^(6 : ℕ)))+(((811082 : ℝ)*(z*((1-z)^(5 : ℕ))))+((2015260 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((2670420 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((1990370 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((791170 : ℝ)*((z^(5 : ℕ))*(1-z)))+((131032 : ℝ)*(z^(6 : ℕ))))))=(((-4978 : ℝ)*z)+(136010 : ℝ)) := by ring
  have hz14 : ((((463135 : ℝ)*((1-z)^(6 : ℕ)))+(((2770952 : ℝ)*(z*((1-z)^(5 : ℕ))))+((6907735 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((9184120 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((6868445 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((2739520 : ℝ)*((z^(5 : ℕ))*(1-z)))+((455277 : ℝ)*(z^(6 : ℕ))))))=(((-7858 : ℝ)*z)+(463135 : ℝ)) := by ring
  have hz15 : ((((716822 : ℝ)*((1-z)^(6 : ℕ)))+(((4299946 : ℝ)*(z*((1-z)^(5 : ℕ))))+((10747400 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((14326580 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((10742470 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((4296002 : ℝ)*((z^(5 : ℕ))*(1-z)))+((715836 : ℝ)*(z^(6 : ℕ))))))=(((-986 : ℝ)*z)+(716822 : ℝ)) := by ring
  have hz16 : ((((503512 : ℝ)*((1-z)^(6 : ℕ)))+(((3029522 : ℝ)*(z*((1-z)^(5 : ℕ))))+((7594930 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((10154740 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((7637180 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((3063322 : ℝ)*((z^(5 : ℕ))*(1-z)))+((511962 : ℝ)*(z^(6 : ℕ))))))=(((8450 : ℝ)*z)+(503512 : ℝ)) := by ring
  have hz17 : ((((129888 : ℝ)*((1-z)^(6 : ℕ)))+(((787028 : ℝ)*(z*((1-z)^(5 : ℕ))))+((1986820 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((2674760 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((2025320 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((817828 : ℝ)*((z^(5 : ℕ))*(1-z)))+((137588 : ℝ)*(z^(6 : ℕ))))))=(((7700 : ℝ)*z)+(129888 : ℝ)) := by ring
  have hz18 : ((((2080 : ℝ)*(z*((1-z)^(5 : ℕ))))+(((10400 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))+((20800 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))))+(((20800 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ))))+(((10400 : ℝ)*((z^(5 : ℕ))*(1-z)))+((2080 : ℝ)*(z^(6 : ℕ))))))=((2080 : ℝ)*z) := by ring
  unfold upperCertificate08Block03
  simp only [hz12,hz13,hz14,hz15,hz16,hz17,hz18]
  unfold upperCertificate08Block03Coeff0 upperCertificate08Block03Coeff1 upperCertificate08Block03Coeff2 upperCertificate08Block03Coeff3 upperCertificate08Block03Coeff4 upperCertificate08Block03Coeff5 upperCertificate08Block03Coeff6
  ring

theorem upperCertificate08Block03_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate08Block03 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate08Block03
  positivity

theorem upperCertificate08Block04_identity (t z : ℝ) :
    upperCertificate08Block04 t z=(((upperCertificate08Block04Coeff0 t)*z^(0 : ℕ)+((upperCertificate08Block04Coeff1 t)*z^(1 : ℕ)+(upperCertificate08Block04Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate08Block04Coeff3 t)*z^(3 : ℕ)+(upperCertificate08Block04Coeff4 t)*z^(4 : ℕ))+((upperCertificate08Block04Coeff5 t)*z^(5 : ℕ)+(upperCertificate08Block04Coeff6 t)*z^(6 : ℕ)))) := by
  have hz11 : ((((43680 : ℝ)*((1-z)^(6 : ℕ)))+(((255840 : ℝ)*(z*((1-z)^(5 : ℕ))))+((624032 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((811328 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((592992 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((231008 : ℝ)*((z^(5 : ℕ))*(1-z)))+((37472 : ℝ)*(z^(6 : ℕ))))))=(((32 : ℝ)*(z^(2 : ℕ)))+(((-6240 : ℝ)*z)+(43680 : ℝ))) := by ring
  have hz12 : ((((535990 : ℝ)*((1-z)^(6 : ℕ)))+(((3164890 : ℝ)*(z*((1-z)^(5 : ℕ))))+((7784728 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((10209812 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((7530118 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((2961202 : ℝ)*((z^(5 : ℕ))*(1-z)))+((485068 : ℝ)*(z^(6 : ℕ))))))=(((128 : ℝ)*(z^(2 : ℕ)))+(((-51050 : ℝ)*z)+(535990 : ℝ))) := by ring
  have hz13 : ((((2509535 : ℝ)*((1-z)^(6 : ℕ)))+(((14908798 : ℝ)*(z*((1-z)^(5 : ℕ))))+((36901061 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((48706964 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((36159481 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((14315534 : ℝ)*((z^(5 : ℕ))*(1-z)))+((2361219 : ℝ)*(z^(6 : ℕ))))))=(((96 : ℝ)*(z^(2 : ℕ)))+(((-148412 : ℝ)*z)+(2509535 : ℝ))) := by ring
  have hz14 : ((((5743675 : ℝ)*((1-z)^(6 : ℕ)))+(((34286518 : ℝ)*(z*((1-z)^(5 : ℕ))))+((85277145 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((113116900 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((84397885 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((33583110 : ℝ)*((z^(5 : ℕ))*(1-z)))+((5567823 : ℝ)*(z^(6 : ℕ))))))=(((-320 : ℝ)*(z^(2 : ℕ)))+(((-175532 : ℝ)*z)+(5743675 : ℝ))) := by ring
  have hz15 : ((((6772295 : ℝ)*((1-z)^(6 : ℕ)))+(((40603418 : ℝ)*(z*((1-z)^(5 : ℕ))))+((101431865 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((135139180 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((101276105 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((40478810 : ℝ)*((z^(5 : ℕ))*(1-z)))+((6741143 : ℝ)*(z^(6 : ℕ))))))=(((-800 : ℝ)*(z^(2 : ℕ)))+(((-30352 : ℝ)*z)+(6772295 : ℝ))) := by ring
  have hz16 : ((((3898228 : ℝ)*((1-z)^(6 : ℕ)))+(((23502822 : ℝ)*(z*((1-z)^(5 : ℕ))))+((59039922 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((79096028 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((59603352 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((23953566 : ℝ)*((z^(5 : ℕ))*(1-z)))+((4010914 : ℝ)*(z^(6 : ℕ))))))=(((-768 : ℝ)*(z^(2 : ℕ)))+(((113454 : ℝ)*z)+(3898228 : ℝ))) := by ring
  have hz17 : ((((861624 : ℝ)*((1-z)^(6 : ℕ)))+(((5265020 : ℝ)*(z*((1-z)^(5 : ℕ))))+((13400388 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((18183832 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((13875008 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((5644716 : ℝ)*((z^(5 : ℕ))*(1-z)))+((956548 : ℝ)*(z^(6 : ℕ))))))=(((-352 : ℝ)*(z^(2 : ℕ)))+(((95276 : ℝ)*z)+(861624 : ℝ))) := by ring
  have hz18 : ((((23400 : ℝ)*(z*((1-z)^(5 : ℕ))))+(((116936 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))+((233744 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))))+(((233616 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ))))+(((116744 : ℝ)*((z^(5 : ℕ))*(1-z)))+((23336 : ℝ)*(z^(6 : ℕ))))))=(((-64 : ℝ)*(z^(2 : ℕ)))+((23400 : ℝ)*z)) := by ring
  unfold upperCertificate08Block04
  simp only [hz11,hz12,hz13,hz14,hz15,hz16,hz17,hz18]
  unfold upperCertificate08Block04Coeff0 upperCertificate08Block04Coeff1 upperCertificate08Block04Coeff2 upperCertificate08Block04Coeff3 upperCertificate08Block04Coeff4 upperCertificate08Block04Coeff5 upperCertificate08Block04Coeff6
  ring

theorem upperCertificate08Block04_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate08Block04 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate08Block04
  positivity

end LeanVerification.PositiveDCompletion
