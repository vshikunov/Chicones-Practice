import LeanVerification.PositiveDCompletion.UpperCertificate09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperCertificate09Block00_identity (t z : ℝ) :
    upperCertificate09Block00 t z=(((upperCertificate09Block00Coeff0 t)*z^(0 : ℕ)+((upperCertificate09Block00Coeff1 t)*z^(1 : ℕ)+(upperCertificate09Block00Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate09Block00Coeff3 t)*z^(3 : ℕ)+(upperCertificate09Block00Coeff4 t)*z^(4 : ℕ))+((upperCertificate09Block00Coeff5 t)*z^(5 : ℕ)+(upperCertificate09Block00Coeff6 t)*z^(6 : ℕ)))) := by
  have hz15 : ((((2 : ℝ)*((1-z)^(6 : ℕ)))+(((12 : ℝ)*(z*((1-z)^(5 : ℕ))))+((30 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((40 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((30 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((12 : ℝ)*((z^(5 : ℕ))*(1-z)))+((2 : ℝ)*(z^(6 : ℕ))))))=(2 : ℝ) := by ring
  have hz16 : ((((4 : ℝ)*((1-z)^(6 : ℕ)))+(((24 : ℝ)*(z*((1-z)^(5 : ℕ))))+((60 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((80 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((60 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((24 : ℝ)*((z^(5 : ℕ))*(1-z)))+((4 : ℝ)*(z^(6 : ℕ))))))=(4 : ℝ) := by ring
  have hz17 : ((((2 : ℝ)*((1-z)^(6 : ℕ)))+(((12 : ℝ)*(z*((1-z)^(5 : ℕ))))+((30 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((40 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((30 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((12 : ℝ)*((z^(5 : ℕ))*(1-z)))+((2 : ℝ)*(z^(6 : ℕ))))))=(2 : ℝ) := by ring
  unfold upperCertificate09Block00
  simp only [hz15,hz16,hz17]
  unfold upperCertificate09Block00Coeff0 upperCertificate09Block00Coeff1 upperCertificate09Block00Coeff2 upperCertificate09Block00Coeff3 upperCertificate09Block00Coeff4 upperCertificate09Block00Coeff5 upperCertificate09Block00Coeff6
  ring

theorem upperCertificate09Block00_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate09Block00 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate09Block00
  positivity

theorem upperCertificate09Block01_identity (t z : ℝ) :
    upperCertificate09Block01 t z=(((upperCertificate09Block01Coeff0 t)*z^(0 : ℕ)+((upperCertificate09Block01Coeff1 t)*z^(1 : ℕ)+(upperCertificate09Block01Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate09Block01Coeff3 t)*z^(3 : ℕ)+(upperCertificate09Block01Coeff4 t)*z^(4 : ℕ))+((upperCertificate09Block01Coeff5 t)*z^(5 : ℕ)+(upperCertificate09Block01Coeff6 t)*z^(6 : ℕ)))) := by
  have hz14 : ((((30 : ℝ)*((1-z)^(6 : ℕ)))+(((180 : ℝ)*(z*((1-z)^(5 : ℕ))))+((450 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((600 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((450 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((180 : ℝ)*((z^(5 : ℕ))*(1-z)))+((30 : ℝ)*(z^(6 : ℕ))))))=(30 : ℝ) := by ring
  have hz15 : ((((128 : ℝ)*((1-z)^(6 : ℕ)))+(((768 : ℝ)*(z*((1-z)^(5 : ℕ))))+((1920 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((2560 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((1920 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((768 : ℝ)*((z^(5 : ℕ))*(1-z)))+((128 : ℝ)*(z^(6 : ℕ))))))=(128 : ℝ) := by ring
  have hz16 : ((((158 : ℝ)*((1-z)^(6 : ℕ)))+(((948 : ℝ)*(z*((1-z)^(5 : ℕ))))+((2370 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((3160 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((2370 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((948 : ℝ)*((z^(5 : ℕ))*(1-z)))+((158 : ℝ)*(z^(6 : ℕ))))))=(158 : ℝ) := by ring
  have hz17 : ((((60 : ℝ)*((1-z)^(6 : ℕ)))+(((360 : ℝ)*(z*((1-z)^(5 : ℕ))))+((900 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((1200 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((900 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((360 : ℝ)*((z^(5 : ℕ))*(1-z)))+((60 : ℝ)*(z^(6 : ℕ))))))=(60 : ℝ) := by ring
  unfold upperCertificate09Block01
  simp only [hz14,hz15,hz16,hz17]
  unfold upperCertificate09Block01Coeff0 upperCertificate09Block01Coeff1 upperCertificate09Block01Coeff2 upperCertificate09Block01Coeff3 upperCertificate09Block01Coeff4 upperCertificate09Block01Coeff5 upperCertificate09Block01Coeff6
  ring

theorem upperCertificate09Block01_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate09Block01 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate09Block01
  positivity

theorem upperCertificate09Block02_identity (t z : ℝ) :
    upperCertificate09Block02 t z=(((upperCertificate09Block02Coeff0 t)*z^(0 : ℕ)+((upperCertificate09Block02Coeff1 t)*z^(1 : ℕ)+(upperCertificate09Block02Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate09Block02Coeff3 t)*z^(3 : ℕ)+(upperCertificate09Block02Coeff4 t)*z^(4 : ℕ))+((upperCertificate09Block02Coeff5 t)*z^(5 : ℕ)+(upperCertificate09Block02Coeff6 t)*z^(6 : ℕ)))) := by
  have hz13 : ((((210 : ℝ)*((1-z)^(6 : ℕ)))+(((1256 : ℝ)*(z*((1-z)^(5 : ℕ))))+((3130 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((4160 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((3110 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((1240 : ℝ)*((z^(5 : ℕ))*(1-z)))+((206 : ℝ)*(z^(6 : ℕ))))))=(((-4 : ℝ)*z)+(210 : ℝ)) := by ring
  have hz14 : ((((1410 : ℝ)*((1-z)^(6 : ℕ)))+(((8452 : ℝ)*(z*((1-z)^(5 : ℕ))))+((21110 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((28120 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((21070 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((8420 : ℝ)*((z^(5 : ℕ))*(1-z)))+((1402 : ℝ)*(z^(6 : ℕ))))))=(((-8 : ℝ)*z)+(1410 : ℝ)) := by ring
  have hz15 : ((((3178 : ℝ)*((1-z)^(6 : ℕ)))+(((19076 : ℝ)*(z*((1-z)^(5 : ℕ))))+((47710 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((63640 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((47750 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((19108 : ℝ)*((z^(5 : ℕ))*(1-z)))+((3186 : ℝ)*(z^(6 : ℕ))))))=(((8 : ℝ)*z)+(3178 : ℝ)) := by ring
  have hz16 : ((((2833 : ℝ)*((1-z)^(6 : ℕ)))+(((17030 : ℝ)*(z*((1-z)^(5 : ℕ))))+((42655 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((56980 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((42815 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((17158 : ℝ)*((z^(5 : ℕ))*(1-z)))+((2865 : ℝ)*(z^(6 : ℕ))))))=(((32 : ℝ)*z)+(2833 : ℝ)) := by ring
  have hz17 : ((((864 : ℝ)*((1-z)^(6 : ℕ)))+(((5212 : ℝ)*(z*((1-z)^(5 : ℕ))))+((13100 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((17560 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((13240 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((5324 : ℝ)*((z^(5 : ℕ))*(1-z)))+((892 : ℝ)*(z^(6 : ℕ))))))=(((28 : ℝ)*z)+(864 : ℝ)) := by ring
  have hz18 : ((((8 : ℝ)*(z*((1-z)^(5 : ℕ))))+(((40 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))+((80 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))))+(((80 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ))))+(((40 : ℝ)*((z^(5 : ℕ))*(1-z)))+((8 : ℝ)*(z^(6 : ℕ))))))=((8 : ℝ)*z) := by ring
  unfold upperCertificate09Block02
  simp only [hz13,hz14,hz15,hz16,hz17,hz18]
  unfold upperCertificate09Block02Coeff0 upperCertificate09Block02Coeff1 upperCertificate09Block02Coeff2 upperCertificate09Block02Coeff3 upperCertificate09Block02Coeff4 upperCertificate09Block02Coeff5 upperCertificate09Block02Coeff6
  ring

theorem upperCertificate09Block02_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate09Block02 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate09Block02
  positivity

theorem upperCertificate09Block03_identity (t z : ℝ) :
    upperCertificate09Block03 t z=(((upperCertificate09Block03Coeff0 t)*z^(0 : ℕ)+((upperCertificate09Block03Coeff1 t)*z^(1 : ℕ)+(upperCertificate09Block03Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate09Block03Coeff3 t)*z^(3 : ℕ)+(upperCertificate09Block03Coeff4 t)*z^(4 : ℕ))+((upperCertificate09Block03Coeff5 t)*z^(5 : ℕ)+(upperCertificate09Block03Coeff6 t)*z^(6 : ℕ)))) := by
  have hz12 : ((((910 : ℝ)*((1-z)^(6 : ℕ)))+(((5403 : ℝ)*(z*((1-z)^(5 : ℕ))))+((13365 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((17630 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((13080 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((5175 : ℝ)*((z^(5 : ℕ))*(1-z)))+((853 : ℝ)*(z^(6 : ℕ))))))=(((-57 : ℝ)*z)+(910 : ℝ)) := by ring
  have hz13 : ((((8540 : ℝ)*((1-z)^(6 : ℕ)))+(((50963 : ℝ)*(z*((1-z)^(5 : ℕ))))+((126715 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((168030 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((125330 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((49855 : ℝ)*((z^(5 : ℕ))*(1-z)))+((8263 : ℝ)*(z^(6 : ℕ))))))=(((-277 : ℝ)*z)+(8540 : ℝ)) := by ring
  have hz14 : ((((29140 : ℝ)*((1-z)^(6 : ℕ)))+(((174537 : ℝ)*(z*((1-z)^(5 : ℕ))))+((435585 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((579770 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((434070 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((173325 : ℝ)*((z^(5 : ℕ))*(1-z)))+((28837 : ℝ)*(z^(6 : ℕ))))))=(((-303 : ℝ)*z)+(29140 : ℝ)) := by ring
  have hz15 : ((((44985 : ℝ)*((1-z)^(6 : ℕ)))+(((270277 : ℝ)*(z*((1-z)^(5 : ℕ))))+((676610 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((903370 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((678445 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((271745 : ℝ)*((z^(5 : ℕ))*(1-z)))+((45352 : ℝ)*(z^(6 : ℕ))))))=(((367 : ℝ)*z)+(44985 : ℝ)) := by ring
  have hz16 : ((((31300 : ℝ)*((1-z)^(6 : ℕ)))+(((188804 : ℝ)*(z*((1-z)^(5 : ℕ))))+((474520 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((636040 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((479540 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((192820 : ℝ)*((z^(5 : ℕ))*(1-z)))+((32304 : ℝ)*(z^(6 : ℕ))))))=(((1004 : ℝ)*z)+(31300 : ℝ)) := by ring
  have hz17 : ((((7954 : ℝ)*((1-z)^(6 : ℕ)))+(((48462 : ℝ)*(z*((1-z)^(5 : ℕ))))+((123000 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((166460 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((126690 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((51414 : ℝ)*((z^(5 : ℕ))*(1-z)))+((8692 : ℝ)*(z^(6 : ℕ))))))=(((738 : ℝ)*z)+(7954 : ℝ)) := by ring
  have hz18 : ((((184 : ℝ)*(z*((1-z)^(5 : ℕ))))+(((920 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))+((1840 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))))+(((1840 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ))))+(((920 : ℝ)*((z^(5 : ℕ))*(1-z)))+((184 : ℝ)*(z^(6 : ℕ))))))=((184 : ℝ)*z) := by ring
  unfold upperCertificate09Block03
  simp only [hz12,hz13,hz14,hz15,hz16,hz17,hz18]
  unfold upperCertificate09Block03Coeff0 upperCertificate09Block03Coeff1 upperCertificate09Block03Coeff2 upperCertificate09Block03Coeff3 upperCertificate09Block03Coeff4 upperCertificate09Block03Coeff5 upperCertificate09Block03Coeff6
  ring

theorem upperCertificate09Block03_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate09Block03 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate09Block03
  positivity

theorem upperCertificate09Block04_identity (t z : ℝ) :
    upperCertificate09Block04 t z=(((upperCertificate09Block04Coeff0 t)*z^(0 : ℕ)+((upperCertificate09Block04Coeff1 t)*z^(1 : ℕ)+(upperCertificate09Block04Coeff2 t)*z^(2 : ℕ)))+(((upperCertificate09Block04Coeff3 t)*z^(3 : ℕ)+(upperCertificate09Block04Coeff4 t)*z^(4 : ℕ))+((upperCertificate09Block04Coeff5 t)*z^(5 : ℕ)+(upperCertificate09Block04Coeff6 t)*z^(6 : ℕ)))) := by
  have hz11 : ((((2730 : ℝ)*((1-z)^(6 : ℕ)))+(((16008 : ℝ)*(z*((1-z)^(5 : ℕ))))+((39090 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((50880 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((37230 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((14520 : ℝ)*((z^(5 : ℕ))*(1-z)))+((2358 : ℝ)*(z^(6 : ℕ))))))=(((-372 : ℝ)*z)+(2730 : ℝ)) := by ring
  have hz12 : ((((33670 : ℝ)*((1-z)^(6 : ℕ)))+(((199092 : ℝ)*(z*((1-z)^(5 : ℕ))))+((490410 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((644120 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((475770 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((187380 : ℝ)*((z^(5 : ℕ))*(1-z)))+((30742 : ℝ)*(z^(6 : ℕ))))))=(((-2928 : ℝ)*z)+(33670 : ℝ)) := by ring
  have hz13 : ((((158200 : ℝ)*((1-z)^(6 : ℕ)))+(((941513 : ℝ)*(z*((1-z)^(5 : ℕ))))+((2334565 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((3087130 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((2296130 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((910765 : ℝ)*((z^(5 : ℕ))*(1-z)))+((150513 : ℝ)*(z^(6 : ℕ))))))=(((-7687 : ℝ)*z)+(158200 : ℝ)) := by ring
  have hz14 : ((((362235 : ℝ)*((1-z)^(6 : ℕ)))+(((2167243 : ℝ)*(z*((1-z)^(5 : ℕ))))+((5402690 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((7183030 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((5371855 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((2142575 : ℝ)*((z^(5 : ℕ))*(1-z)))+((356068 : ℝ)*(z^(6 : ℕ))))))=(((-6167 : ℝ)*z)+(362235 : ℝ)) := by ring
  have hz15 : ((((425165 : ℝ)*((1-z)^(6 : ℕ)))+(((2556855 : ℝ)*(z*((1-z)^(5 : ℕ))))+((6406800 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((8561950 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((6436125 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((2580315 : ℝ)*((z^(5 : ℕ))*(1-z)))+((431030 : ℝ)*(z^(6 : ℕ))))))=(((5865 : ℝ)*z)+(425165 : ℝ)) := by ring
  have hz16 : ((((241970 : ℝ)*((1-z)^(6 : ℕ)))+(((1465723 : ℝ)*(z*((1-z)^(5 : ℕ))))+((3699065 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((4978430 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((3768580 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((1521335 : ℝ)*((z^(5 : ℕ))*(1-z)))+((255873 : ℝ)*(z^(6 : ℕ))))))=(((13903 : ℝ)*z)+(241970 : ℝ)) := by ring
  have hz17 : ((((52602 : ℝ)*((1-z)^(6 : ℕ)))+(((324626 : ℝ)*(z*((1-z)^(5 : ℕ))))+((834100 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))))+((((1142180 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))+((879170 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ)))))+(((360682 : ℝ)*((z^(5 : ℕ))*(1-z)))+((61616 : ℝ)*(z^(6 : ℕ))))))=(((9014 : ℝ)*z)+(52602 : ℝ)) := by ring
  have hz18 : ((((2012 : ℝ)*(z*((1-z)^(5 : ℕ))))+(((10060 : ℝ)*((z^(2 : ℕ))*((1-z)^(4 : ℕ))))+((20120 : ℝ)*((z^(3 : ℕ))*((1-z)^(3 : ℕ))))))+(((20120 : ℝ)*((z^(4 : ℕ))*((1-z)^(2 : ℕ))))+(((10060 : ℝ)*((z^(5 : ℕ))*(1-z)))+((2012 : ℝ)*(z^(6 : ℕ))))))=((2012 : ℝ)*z) := by ring
  unfold upperCertificate09Block04
  simp only [hz11,hz12,hz13,hz14,hz15,hz16,hz17,hz18]
  unfold upperCertificate09Block04Coeff0 upperCertificate09Block04Coeff1 upperCertificate09Block04Coeff2 upperCertificate09Block04Coeff3 upperCertificate09Block04Coeff4 upperCertificate09Block04Coeff5 upperCertificate09Block04Coeff6
  ring

theorem upperCertificate09Block04_pos {t z : ℝ} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :
    0<upperCertificate09Block04 t z := by
  have htc : 0<1-t := by linarith
  have hzc : 0<1-z := by linarith
  unfold upperCertificate09Block04
  positivity

end LeanVerification.PositiveDCompletion
