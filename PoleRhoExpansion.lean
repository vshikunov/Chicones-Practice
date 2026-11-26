import LeanVerification.PositiveDCompletion.PoleRhoData

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 64000000
set_option maxRecDepth 60000

theorem poleRhoOne_eval (a f rho : ℝ) :
    poleRhoOne a f rho=(poleRhoOneCoeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoOne poleRhoOneCoeff0
  ring

theorem poleRhoVariable_eval (a f rho : ℝ) :
    poleRhoVariable a f rho=((poleRhoVariableCoeff0 a f)*(rho)^(0 : ℕ)+(poleRhoVariableCoeff1 a f)*(rho)^(1 : ℕ)) := by
  unfold poleRhoVariable poleRhoVariableCoeff0 poleRhoVariableCoeff1
  ring

theorem poleRhoBase_eval (a f rho : ℝ) :
    poleRhoBase a f rho=((poleRhoBaseCoeff0 a f)*(rho)^(0 : ℕ)+(poleRhoBaseCoeff1 a f)*(rho)^(1 : ℕ)) := by
  unfold poleRhoBase poleRhoBaseCoeff0 poleRhoBaseCoeff1 sourceBase modelG
  ring

theorem poleRhoC_eval (a f rho : ℝ) :
    poleRhoC a f rho=((poleRhoCCoeff0 a f)*(rho)^(0 : ℕ)+(poleRhoCCoeff1 a f)*(rho)^(1 : ℕ)) := by
  unfold poleRhoC poleRhoCCoeff0 poleRhoCCoeff1 sourceC
  ring

theorem poleRhoG_eval (a f rho : ℝ) :
    poleRhoG a f rho=((poleRhoGCoeff0 a f)*(rho)^(0 : ℕ)+(poleRhoGCoeff1 a f)*(rho)^(1 : ℕ)) := by
  unfold poleRhoG poleRhoGCoeff0 poleRhoGCoeff1
  ring

theorem poleRhoS_eval (a f rho : ℝ) :
    poleRhoS a f rho=((poleRhoSCoeff0 a f)*(rho)^(0 : ℕ)+(poleRhoSCoeff1 a f)*(rho)^(1 : ℕ)) := by
  unfold poleRhoS poleRhoSCoeff0 poleRhoSCoeff1
  ring

theorem poleRhoRaw0_eval (a f rho : ℝ) :
    poleRhoRaw0 a f rho=(((poleRhoRaw0Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoRaw0Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoRaw0Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoRaw0Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoRaw0Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoRaw0Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoRaw0Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoRaw0 poleRhoRaw0Coeff0 poleRhoRaw0Coeff1 poleRhoRaw0Coeff2 poleRhoRaw0Coeff3 poleRhoRaw0Coeff4 poleRhoRaw0Coeff5 poleRhoRaw0Coeff6 rxNumCoeff0
  ring

theorem poleRhoRaw1_eval (a f rho : ℝ) :
    poleRhoRaw1 a f rho=(((poleRhoRaw1Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoRaw1Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoRaw1Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoRaw1Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoRaw1Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoRaw1Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoRaw1Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoRaw1 poleRhoRaw1Coeff0 poleRhoRaw1Coeff1 poleRhoRaw1Coeff2 poleRhoRaw1Coeff3 poleRhoRaw1Coeff4 poleRhoRaw1Coeff5 poleRhoRaw1Coeff6 rxNumCoeff1
  ring

theorem poleRhoRaw2_eval (a f rho : ℝ) :
    poleRhoRaw2 a f rho=(((poleRhoRaw2Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoRaw2Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoRaw2Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoRaw2Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoRaw2Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoRaw2Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoRaw2Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoRaw2 poleRhoRaw2Coeff0 poleRhoRaw2Coeff1 poleRhoRaw2Coeff2 poleRhoRaw2Coeff3 poleRhoRaw2Coeff4 poleRhoRaw2Coeff5 poleRhoRaw2Coeff6 rxNumCoeff2
  ring

theorem poleRhoRaw3_eval (a f rho : ℝ) :
    poleRhoRaw3 a f rho=(((poleRhoRaw3Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoRaw3Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoRaw3Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoRaw3Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoRaw3Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoRaw3Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoRaw3Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoRaw3 poleRhoRaw3Coeff0 poleRhoRaw3Coeff1 poleRhoRaw3Coeff2 poleRhoRaw3Coeff3 poleRhoRaw3Coeff4 poleRhoRaw3Coeff5 poleRhoRaw3Coeff6 rxNumCoeff3
  ring

theorem poleRhoRaw4_eval (a f rho : ℝ) :
    poleRhoRaw4 a f rho=(((poleRhoRaw4Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoRaw4Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoRaw4Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoRaw4Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoRaw4Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoRaw4Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoRaw4Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoRaw4 poleRhoRaw4Coeff0 poleRhoRaw4Coeff1 poleRhoRaw4Coeff2 poleRhoRaw4Coeff3 poleRhoRaw4Coeff4 poleRhoRaw4Coeff5 poleRhoRaw4Coeff6 rxNumCoeff4
  ring

theorem poleRhoRaw5_eval (a f rho : ℝ) :
    poleRhoRaw5 a f rho=(((poleRhoRaw5Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoRaw5Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoRaw5Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoRaw5Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoRaw5Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoRaw5Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoRaw5Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoRaw5 poleRhoRaw5Coeff0 poleRhoRaw5Coeff1 poleRhoRaw5Coeff2 poleRhoRaw5Coeff3 poleRhoRaw5Coeff4 poleRhoRaw5Coeff5 poleRhoRaw5Coeff6 rxNumCoeff5
  ring

theorem poleRhoRaw6_eval (a f rho : ℝ) :
    poleRhoRaw6 a f rho=(((poleRhoRaw6Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoRaw6Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoRaw6Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoRaw6Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoRaw6Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoRaw6Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoRaw6Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoRaw6 poleRhoRaw6Coeff0 poleRhoRaw6Coeff1 poleRhoRaw6Coeff2 poleRhoRaw6Coeff3 poleRhoRaw6Coeff4 poleRhoRaw6Coeff5 poleRhoRaw6Coeff6 rxNumCoeff6
  ring

theorem poleRhoUpper1_eval (a f rho : ℝ) :
    poleRhoUpper1 a f rho=(((poleRhoUpper1Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoUpper1Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoUpper1Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoUpper1Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoUpper1 poleRhoUpper1Coeff0 poleRhoUpper1Coeff1 poleRhoUpper1Coeff2 poleRhoUpper1Coeff3 upperNum01
  ring

theorem poleRhoUpper2_eval (a f rho : ℝ) :
    poleRhoUpper2 a f rho=(((poleRhoUpper2Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoUpper2Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoUpper2Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoUpper2Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoUpper2Coeff4 a f)*(rho)^(4 : ℕ)))) := by
  unfold poleRhoUpper2 poleRhoUpper2Coeff0 poleRhoUpper2Coeff1 poleRhoUpper2Coeff2 poleRhoUpper2Coeff3 poleRhoUpper2Coeff4 upperNum02
  ring

theorem poleRhoUpper3_eval (a f rho : ℝ) :
    poleRhoUpper3 a f rho=(((poleRhoUpper3Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoUpper3Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoUpper3Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoUpper3Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoUpper3Coeff4 a f)*(rho)^(4 : ℕ)))) := by
  unfold poleRhoUpper3 poleRhoUpper3Coeff0 poleRhoUpper3Coeff1 poleRhoUpper3Coeff2 poleRhoUpper3Coeff3 poleRhoUpper3Coeff4 upperNum03 upperNum03Coeff0 upperNum03Coeff1 upperNum03Coeff2 upperNum03Coeff3 upperNum03Coeff4
  ring

theorem poleRhoUpper4_eval (a f rho : ℝ) :
    poleRhoUpper4 a f rho=(((poleRhoUpper4Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoUpper4Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoUpper4Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoUpper4Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoUpper4Coeff4 a f)*(rho)^(4 : ℕ)))) := by
  unfold poleRhoUpper4 poleRhoUpper4Coeff0 poleRhoUpper4Coeff1 poleRhoUpper4Coeff2 poleRhoUpper4Coeff3 poleRhoUpper4Coeff4 upperNum04 upperNum04Coeff0 upperNum04Coeff1 upperNum04Coeff2 upperNum04Coeff3 upperNum04Coeff4
  ring

theorem poleRhoUpper5_eval (a f rho : ℝ) :
    poleRhoUpper5 a f rho=(((poleRhoUpper5Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoUpper5Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoUpper5Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoUpper5Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoUpper5Coeff4 a f)*(rho)^(4 : ℕ)))) := by
  unfold poleRhoUpper5 poleRhoUpper5Coeff0 poleRhoUpper5Coeff1 poleRhoUpper5Coeff2 poleRhoUpper5Coeff3 poleRhoUpper5Coeff4 upperNum05 upperNum05Coeff0 upperNum05Coeff1 upperNum05Coeff2 upperNum05Coeff3 upperNum05Coeff4
  ring

theorem poleRhoCore0_eval (a f rho : ℝ) :
    poleRhoCore0 a f rho=((poleRhoCore0Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoCore0Coeff1 a f)*(rho)^(1 : ℕ)) := by
  unfold poleRhoCore0 poleRhoCore0Coeff0 poleRhoCore0Coeff1 poleCore00
  ring

theorem poleRhoCore4_eval (a f rho : ℝ) :
    poleRhoCore4 a f rho=(((poleRhoCore4Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoCore4Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoCore4Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoCore4Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoCore4 poleRhoCore4Coeff0 poleRhoCore4Coeff1 poleRhoCore4Coeff2 poleRhoCore4Coeff3 poleCore04
  ring

theorem poleRhoInvariant0_eval (a f rho : ℝ) :
    poleRhoInvariant0 a f rho=(poleRhoInvariant0Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoInvariant0 poleRhoInvariant0Coeff0
  ring

theorem poleRhoNode021_eval (a f rho : ℝ) :
    poleRhoNode021 a f rho=((poleRhoNode021Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode021Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode021Coeff2 a f)*(rho)^(2 : ℕ))) := by
  unfold poleRhoNode021
  rw [poleRhoVariable_eval]
  simpa only [poleRhoNode021Coeff0,poleRhoNode021Coeff1,poleRhoNode021Coeff2] using
    pole_rho_mul_1_1 rho (poleRhoVariableCoeff0 a f) (poleRhoVariableCoeff1 a f) (poleRhoVariableCoeff0 a f) (poleRhoVariableCoeff1 a f)

theorem poleRhoNode022_eval (a f rho : ℝ) :
    poleRhoNode022 a f rho=(((poleRhoNode022Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode022Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode022Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode022Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode022
  rw [poleRhoNode021_eval,poleRhoVariable_eval]
  simpa only [poleRhoNode022Coeff0,poleRhoNode022Coeff1,poleRhoNode022Coeff2,poleRhoNode022Coeff3] using
    pole_rho_mul_2_1 rho (poleRhoNode021Coeff0 a f) (poleRhoNode021Coeff1 a f) (poleRhoNode021Coeff2 a f) (poleRhoVariableCoeff0 a f) (poleRhoVariableCoeff1 a f)

theorem poleRhoNode023_eval (a f rho : ℝ) :
    poleRhoNode023 a f rho=((poleRhoNode023Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode023Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode023Coeff2 a f)*(rho)^(2 : ℕ))) := by
  unfold poleRhoNode023
  rw [poleRhoG_eval]
  simpa only [poleRhoNode023Coeff0,poleRhoNode023Coeff1,poleRhoNode023Coeff2] using
    pole_rho_mul_1_1 rho (poleRhoGCoeff0 a f) (poleRhoGCoeff1 a f) (poleRhoGCoeff0 a f) (poleRhoGCoeff1 a f)

theorem poleRhoNode024_eval (a f rho : ℝ) :
    poleRhoNode024 a f rho=(((poleRhoNode024Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode024Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode024Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode024Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode024
  rw [poleRhoNode023_eval,poleRhoG_eval]
  simpa only [poleRhoNode024Coeff0,poleRhoNode024Coeff1,poleRhoNode024Coeff2,poleRhoNode024Coeff3] using
    pole_rho_mul_2_1 rho (poleRhoNode023Coeff0 a f) (poleRhoNode023Coeff1 a f) (poleRhoNode023Coeff2 a f) (poleRhoGCoeff0 a f) (poleRhoGCoeff1 a f)

theorem poleRhoNode025_eval (a f rho : ℝ) :
    poleRhoNode025 a f rho=((poleRhoNode025Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode025Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode025Coeff2 a f)*(rho)^(2 : ℕ))) := by
  unfold poleRhoNode025
  rw [poleRhoS_eval]
  simpa only [poleRhoNode025Coeff0,poleRhoNode025Coeff1,poleRhoNode025Coeff2] using
    pole_rho_mul_1_1 rho (poleRhoSCoeff0 a f) (poleRhoSCoeff1 a f) (poleRhoSCoeff0 a f) (poleRhoSCoeff1 a f)

theorem poleRhoNode026_eval (a f rho : ℝ) :
    poleRhoNode026 a f rho=(((poleRhoNode026Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode026Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode026Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode026Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode026Coeff4 a f)*(rho)^(4 : ℕ)))) := by
  unfold poleRhoNode026
  rw [poleRhoNode025_eval]
  simpa only [poleRhoNode026Coeff0,poleRhoNode026Coeff1,poleRhoNode026Coeff2,poleRhoNode026Coeff3,poleRhoNode026Coeff4] using
    pole_rho_mul_2_2 rho (poleRhoNode025Coeff0 a f) (poleRhoNode025Coeff1 a f) (poleRhoNode025Coeff2 a f) (poleRhoNode025Coeff0 a f) (poleRhoNode025Coeff1 a f) (poleRhoNode025Coeff2 a f)

theorem poleRhoNode027_eval (a f rho : ℝ) :
    poleRhoNode027 a f rho=((poleRhoNode027Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode027Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode027Coeff2 a f)*(rho)^(2 : ℕ))) := by
  unfold poleRhoNode027
  rw [poleRhoCore0_eval]
  simpa only [poleRhoNode027Coeff0,poleRhoNode027Coeff1,poleRhoNode027Coeff2] using
    pole_rho_mul_1_1 rho (poleRhoCore0Coeff0 a f) (poleRhoCore0Coeff1 a f) (poleRhoCore0Coeff0 a f) (poleRhoCore0Coeff1 a f)

theorem poleRhoNode028_eval (a f rho : ℝ) :
    poleRhoNode028 a f rho=(((poleRhoNode028Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode028Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode028Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode028Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode028
  rw [poleRhoInvariant0_eval,poleRhoNode022_eval]
  simpa only [poleRhoNode028Coeff0,poleRhoNode028Coeff1,poleRhoNode028Coeff2,poleRhoNode028Coeff3] using
    pole_rho_mul_0_3 rho (poleRhoInvariant0Coeff0 a f) (poleRhoNode022Coeff0 a f) (poleRhoNode022Coeff1 a f) (poleRhoNode022Coeff2 a f) (poleRhoNode022Coeff3 a f)

theorem poleRhoNode029_eval (a f rho : ℝ) :
    poleRhoNode029 a f rho=(((poleRhoNode029Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode029Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode029Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoNode029Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode029Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoNode029Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode029Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoNode029
  rw [poleRhoNode026_eval,poleRhoNode027_eval]
  simpa only [poleRhoNode029Coeff0,poleRhoNode029Coeff1,poleRhoNode029Coeff2,poleRhoNode029Coeff3,poleRhoNode029Coeff4,poleRhoNode029Coeff5,poleRhoNode029Coeff6] using
    pole_rho_mul_4_2 rho (poleRhoNode026Coeff0 a f) (poleRhoNode026Coeff1 a f) (poleRhoNode026Coeff2 a f) (poleRhoNode026Coeff3 a f) (poleRhoNode026Coeff4 a f) (poleRhoNode027Coeff0 a f) (poleRhoNode027Coeff1 a f) (poleRhoNode027Coeff2 a f)

theorem poleRhoNode030_eval (a f rho : ℝ) :
    poleRhoNode030 a f rho=((((poleRhoNode030Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode030Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode030Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode030Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode030Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode030Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode030Coeff6 a f)*(rho)^(6 : ℕ))+((poleRhoNode030Coeff7 a f)*(rho)^(7 : ℕ)+((poleRhoNode030Coeff8 a f)*(rho)^(8 : ℕ)+(poleRhoNode030Coeff9 a f)*(rho)^(9 : ℕ))))) := by
  unfold poleRhoNode030
  rw [poleRhoNode024_eval,poleRhoNode029_eval]
  simpa only [poleRhoNode030Coeff0,poleRhoNode030Coeff1,poleRhoNode030Coeff2,poleRhoNode030Coeff3,poleRhoNode030Coeff4,poleRhoNode030Coeff5,poleRhoNode030Coeff6,poleRhoNode030Coeff7,poleRhoNode030Coeff8,poleRhoNode030Coeff9] using
    pole_rho_mul_3_6 rho (poleRhoNode024Coeff0 a f) (poleRhoNode024Coeff1 a f) (poleRhoNode024Coeff2 a f) (poleRhoNode024Coeff3 a f) (poleRhoNode029Coeff0 a f) (poleRhoNode029Coeff1 a f) (poleRhoNode029Coeff2 a f) (poleRhoNode029Coeff3 a f) (poleRhoNode029Coeff4 a f) (poleRhoNode029Coeff5 a f) (poleRhoNode029Coeff6 a f)

theorem poleRhoNode031_eval (a f rho : ℝ) :
    poleRhoNode031 a f rho=((((poleRhoNode031Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode031Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode031Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode031Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode031Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode031Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode031Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode031Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode031Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode031Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode031Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode031Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode031Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode031
  rw [poleRhoNode028_eval,poleRhoNode030_eval]
  simpa only [poleRhoNode031Coeff0,poleRhoNode031Coeff1,poleRhoNode031Coeff2,poleRhoNode031Coeff3,poleRhoNode031Coeff4,poleRhoNode031Coeff5,poleRhoNode031Coeff6,poleRhoNode031Coeff7,poleRhoNode031Coeff8,poleRhoNode031Coeff9,poleRhoNode031Coeff10,poleRhoNode031Coeff11,poleRhoNode031Coeff12] using
    pole_rho_mul_3_9 rho (poleRhoNode028Coeff0 a f) (poleRhoNode028Coeff1 a f) (poleRhoNode028Coeff2 a f) (poleRhoNode028Coeff3 a f) (poleRhoNode030Coeff0 a f) (poleRhoNode030Coeff1 a f) (poleRhoNode030Coeff2 a f) (poleRhoNode030Coeff3 a f) (poleRhoNode030Coeff4 a f) (poleRhoNode030Coeff5 a f) (poleRhoNode030Coeff6 a f) (poleRhoNode030Coeff7 a f) (poleRhoNode030Coeff8 a f) (poleRhoNode030Coeff9 a f)

theorem poleRhoScalar00_eval (a f rho : ℝ) :
    poleRhoScalar00 a f rho=(poleRhoScalar00Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar00 poleRhoScalar00Coeff0
  ring

theorem poleRhoNode033_eval (a f rho : ℝ) :
    poleRhoNode033 a f rho=((poleRhoNode033Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode033Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode033Coeff2 a f)*(rho)^(2 : ℕ))) := by
  unfold poleRhoNode033
  rw [poleRhoC_eval]
  simpa only [poleRhoNode033Coeff0,poleRhoNode033Coeff1,poleRhoNode033Coeff2] using
    pole_rho_mul_1_1 rho (poleRhoCCoeff0 a f) (poleRhoCCoeff1 a f) (poleRhoCCoeff0 a f) (poleRhoCCoeff1 a f)

theorem poleRhoNode034_eval (a f rho : ℝ) :
    poleRhoNode034 a f rho=(((poleRhoNode034Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode034Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode034Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode034Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode034
  rw [poleRhoNode033_eval,poleRhoC_eval]
  simpa only [poleRhoNode034Coeff0,poleRhoNode034Coeff1,poleRhoNode034Coeff2,poleRhoNode034Coeff3] using
    pole_rho_mul_2_1 rho (poleRhoNode033Coeff0 a f) (poleRhoNode033Coeff1 a f) (poleRhoNode033Coeff2 a f) (poleRhoCCoeff0 a f) (poleRhoCCoeff1 a f)

theorem poleRhoNode035_eval (a f rho : ℝ) :
    poleRhoNode035 a f rho=(((poleRhoNode035Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode035Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode035Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoNode035Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode035Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoNode035Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode035Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoNode035
  rw [poleRhoNode034_eval]
  simpa only [poleRhoNode035Coeff0,poleRhoNode035Coeff1,poleRhoNode035Coeff2,poleRhoNode035Coeff3,poleRhoNode035Coeff4,poleRhoNode035Coeff5,poleRhoNode035Coeff6] using
    pole_rho_mul_3_3 rho (poleRhoNode034Coeff0 a f) (poleRhoNode034Coeff1 a f) (poleRhoNode034Coeff2 a f) (poleRhoNode034Coeff3 a f) (poleRhoNode034Coeff0 a f) (poleRhoNode034Coeff1 a f) (poleRhoNode034Coeff2 a f) (poleRhoNode034Coeff3 a f)

theorem poleRhoNode036_eval (a f rho : ℝ) :
    poleRhoNode036 a f rho=(poleRhoNode036Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoNode036
  rw [poleRhoScalar00_eval,poleRhoOne_eval]
  simpa only [poleRhoNode036Coeff0] using
    pole_rho_mul_0_0 rho (poleRhoScalar00Coeff0 a f) (poleRhoOneCoeff0 a f)

theorem poleRhoNode037_eval (a f rho : ℝ) :
    poleRhoNode037 a f rho=((((poleRhoNode037Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode037Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode037Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode037Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode037Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode037Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode037Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode037Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode037Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode037Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode037Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode037Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode037Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode037
  rw [poleRhoNode035_eval,poleRhoRaw0_eval]
  simpa only [poleRhoNode037Coeff0,poleRhoNode037Coeff1,poleRhoNode037Coeff2,poleRhoNode037Coeff3,poleRhoNode037Coeff4,poleRhoNode037Coeff5,poleRhoNode037Coeff6,poleRhoNode037Coeff7,poleRhoNode037Coeff8,poleRhoNode037Coeff9,poleRhoNode037Coeff10,poleRhoNode037Coeff11,poleRhoNode037Coeff12] using
    pole_rho_mul_6_6 rho (poleRhoNode035Coeff0 a f) (poleRhoNode035Coeff1 a f) (poleRhoNode035Coeff2 a f) (poleRhoNode035Coeff3 a f) (poleRhoNode035Coeff4 a f) (poleRhoNode035Coeff5 a f) (poleRhoNode035Coeff6 a f) (poleRhoRaw0Coeff0 a f) (poleRhoRaw0Coeff1 a f) (poleRhoRaw0Coeff2 a f) (poleRhoRaw0Coeff3 a f) (poleRhoRaw0Coeff4 a f) (poleRhoRaw0Coeff5 a f) (poleRhoRaw0Coeff6 a f)

theorem poleRhoNode038_eval (a f rho : ℝ) :
    poleRhoNode038 a f rho=((((poleRhoNode038Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode038Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode038Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode038Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode038Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode038Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode038Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode038Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode038Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode038Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode038Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode038Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode038Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode038
  rw [poleRhoNode036_eval,poleRhoNode037_eval]
  simpa only [poleRhoNode038Coeff0,poleRhoNode038Coeff1,poleRhoNode038Coeff2,poleRhoNode038Coeff3,poleRhoNode038Coeff4,poleRhoNode038Coeff5,poleRhoNode038Coeff6,poleRhoNode038Coeff7,poleRhoNode038Coeff8,poleRhoNode038Coeff9,poleRhoNode038Coeff10,poleRhoNode038Coeff11,poleRhoNode038Coeff12] using
    pole_rho_mul_0_12 rho (poleRhoNode036Coeff0 a f) (poleRhoNode037Coeff0 a f) (poleRhoNode037Coeff1 a f) (poleRhoNode037Coeff2 a f) (poleRhoNode037Coeff3 a f) (poleRhoNode037Coeff4 a f) (poleRhoNode037Coeff5 a f) (poleRhoNode037Coeff6 a f) (poleRhoNode037Coeff7 a f) (poleRhoNode037Coeff8 a f) (poleRhoNode037Coeff9 a f) (poleRhoNode037Coeff10 a f) (poleRhoNode037Coeff11 a f) (poleRhoNode037Coeff12 a f)

theorem poleRhoScalar01_eval (a f rho : ℝ) :
    poleRhoScalar01 a f rho=(poleRhoScalar01Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar01 poleRhoScalar01Coeff0
  ring

theorem poleRhoNode040_eval (a f rho : ℝ) :
    poleRhoNode040 a f rho=(((poleRhoNode040Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode040Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode040Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode040Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode040Coeff4 a f)*(rho)^(4 : ℕ)))) := by
  unfold poleRhoNode040
  rw [poleRhoNode033_eval]
  simpa only [poleRhoNode040Coeff0,poleRhoNode040Coeff1,poleRhoNode040Coeff2,poleRhoNode040Coeff3,poleRhoNode040Coeff4] using
    pole_rho_mul_2_2 rho (poleRhoNode033Coeff0 a f) (poleRhoNode033Coeff1 a f) (poleRhoNode033Coeff2 a f) (poleRhoNode033Coeff0 a f) (poleRhoNode033Coeff1 a f) (poleRhoNode033Coeff2 a f)

theorem poleRhoNode041_eval (a f rho : ℝ) :
    poleRhoNode041 a f rho=(((poleRhoNode041Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode041Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode041Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode041Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode041Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode041Coeff5 a f)*(rho)^(5 : ℕ)))) := by
  unfold poleRhoNode041
  rw [poleRhoNode040_eval,poleRhoC_eval]
  simpa only [poleRhoNode041Coeff0,poleRhoNode041Coeff1,poleRhoNode041Coeff2,poleRhoNode041Coeff3,poleRhoNode041Coeff4,poleRhoNode041Coeff5] using
    pole_rho_mul_4_1 rho (poleRhoNode040Coeff0 a f) (poleRhoNode040Coeff1 a f) (poleRhoNode040Coeff2 a f) (poleRhoNode040Coeff3 a f) (poleRhoNode040Coeff4 a f) (poleRhoCCoeff0 a f) (poleRhoCCoeff1 a f)

theorem poleRhoNode042_eval (a f rho : ℝ) :
    poleRhoNode042 a f rho=((poleRhoNode042Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode042Coeff1 a f)*(rho)^(1 : ℕ)) := by
  unfold poleRhoNode042
  rw [poleRhoScalar01_eval,poleRhoBase_eval]
  simpa only [poleRhoNode042Coeff0,poleRhoNode042Coeff1] using
    pole_rho_mul_0_1 rho (poleRhoScalar01Coeff0 a f) (poleRhoBaseCoeff0 a f) (poleRhoBaseCoeff1 a f)

theorem poleRhoNode043_eval (a f rho : ℝ) :
    poleRhoNode043 a f rho=((((poleRhoNode043Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode043Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode043Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode043Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode043Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode043Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode043Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode043Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode043Coeff8 a f)*(rho)^(8 : ℕ)))+((poleRhoNode043Coeff9 a f)*(rho)^(9 : ℕ)+((poleRhoNode043Coeff10 a f)*(rho)^(10 : ℕ)+(poleRhoNode043Coeff11 a f)*(rho)^(11 : ℕ))))) := by
  unfold poleRhoNode043
  rw [poleRhoNode041_eval,poleRhoRaw1_eval]
  simpa only [poleRhoNode043Coeff0,poleRhoNode043Coeff1,poleRhoNode043Coeff2,poleRhoNode043Coeff3,poleRhoNode043Coeff4,poleRhoNode043Coeff5,poleRhoNode043Coeff6,poleRhoNode043Coeff7,poleRhoNode043Coeff8,poleRhoNode043Coeff9,poleRhoNode043Coeff10,poleRhoNode043Coeff11] using
    pole_rho_mul_5_6 rho (poleRhoNode041Coeff0 a f) (poleRhoNode041Coeff1 a f) (poleRhoNode041Coeff2 a f) (poleRhoNode041Coeff3 a f) (poleRhoNode041Coeff4 a f) (poleRhoNode041Coeff5 a f) (poleRhoRaw1Coeff0 a f) (poleRhoRaw1Coeff1 a f) (poleRhoRaw1Coeff2 a f) (poleRhoRaw1Coeff3 a f) (poleRhoRaw1Coeff4 a f) (poleRhoRaw1Coeff5 a f) (poleRhoRaw1Coeff6 a f)

theorem poleRhoNode044_eval (a f rho : ℝ) :
    poleRhoNode044 a f rho=((((poleRhoNode044Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode044Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode044Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode044Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode044Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode044Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode044Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode044Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode044Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode044Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode044Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode044Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode044Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode044
  rw [poleRhoNode042_eval,poleRhoNode043_eval]
  simpa only [poleRhoNode044Coeff0,poleRhoNode044Coeff1,poleRhoNode044Coeff2,poleRhoNode044Coeff3,poleRhoNode044Coeff4,poleRhoNode044Coeff5,poleRhoNode044Coeff6,poleRhoNode044Coeff7,poleRhoNode044Coeff8,poleRhoNode044Coeff9,poleRhoNode044Coeff10,poleRhoNode044Coeff11,poleRhoNode044Coeff12] using
    pole_rho_mul_1_11 rho (poleRhoNode042Coeff0 a f) (poleRhoNode042Coeff1 a f) (poleRhoNode043Coeff0 a f) (poleRhoNode043Coeff1 a f) (poleRhoNode043Coeff2 a f) (poleRhoNode043Coeff3 a f) (poleRhoNode043Coeff4 a f) (poleRhoNode043Coeff5 a f) (poleRhoNode043Coeff6 a f) (poleRhoNode043Coeff7 a f) (poleRhoNode043Coeff8 a f) (poleRhoNode043Coeff9 a f) (poleRhoNode043Coeff10 a f) (poleRhoNode043Coeff11 a f)

theorem poleRhoScalar02_eval (a f rho : ℝ) :
    poleRhoScalar02 a f rho=(poleRhoScalar02Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar02 poleRhoScalar02Coeff0
  ring

theorem poleRhoNode046_eval (a f rho : ℝ) :
    poleRhoNode046 a f rho=((poleRhoNode046Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode046Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode046Coeff2 a f)*(rho)^(2 : ℕ))) := by
  unfold poleRhoNode046
  rw [poleRhoBase_eval]
  simpa only [poleRhoNode046Coeff0,poleRhoNode046Coeff1,poleRhoNode046Coeff2] using
    pole_rho_mul_1_1 rho (poleRhoBaseCoeff0 a f) (poleRhoBaseCoeff1 a f) (poleRhoBaseCoeff0 a f) (poleRhoBaseCoeff1 a f)

theorem poleRhoNode047_eval (a f rho : ℝ) :
    poleRhoNode047 a f rho=((poleRhoNode047Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode047Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode047Coeff2 a f)*(rho)^(2 : ℕ))) := by
  unfold poleRhoNode047
  rw [poleRhoScalar02_eval,poleRhoNode046_eval]
  simpa only [poleRhoNode047Coeff0,poleRhoNode047Coeff1,poleRhoNode047Coeff2] using
    pole_rho_mul_0_2 rho (poleRhoScalar02Coeff0 a f) (poleRhoNode046Coeff0 a f) (poleRhoNode046Coeff1 a f) (poleRhoNode046Coeff2 a f)

theorem poleRhoNode048_eval (a f rho : ℝ) :
    poleRhoNode048 a f rho=((((poleRhoNode048Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode048Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode048Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode048Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode048Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode048Coeff5 a f)*(rho)^(5 : ℕ)+((poleRhoNode048Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode048Coeff7 a f)*(rho)^(7 : ℕ)))+((poleRhoNode048Coeff8 a f)*(rho)^(8 : ℕ)+((poleRhoNode048Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode048Coeff10 a f)*(rho)^(10 : ℕ))))) := by
  unfold poleRhoNode048
  rw [poleRhoNode040_eval,poleRhoRaw2_eval]
  simpa only [poleRhoNode048Coeff0,poleRhoNode048Coeff1,poleRhoNode048Coeff2,poleRhoNode048Coeff3,poleRhoNode048Coeff4,poleRhoNode048Coeff5,poleRhoNode048Coeff6,poleRhoNode048Coeff7,poleRhoNode048Coeff8,poleRhoNode048Coeff9,poleRhoNode048Coeff10] using
    pole_rho_mul_4_6 rho (poleRhoNode040Coeff0 a f) (poleRhoNode040Coeff1 a f) (poleRhoNode040Coeff2 a f) (poleRhoNode040Coeff3 a f) (poleRhoNode040Coeff4 a f) (poleRhoRaw2Coeff0 a f) (poleRhoRaw2Coeff1 a f) (poleRhoRaw2Coeff2 a f) (poleRhoRaw2Coeff3 a f) (poleRhoRaw2Coeff4 a f) (poleRhoRaw2Coeff5 a f) (poleRhoRaw2Coeff6 a f)

theorem poleRhoNode049_eval (a f rho : ℝ) :
    poleRhoNode049 a f rho=((((poleRhoNode049Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode049Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode049Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode049Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode049Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode049Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode049Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode049Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode049Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode049Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode049Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode049Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode049Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode049
  rw [poleRhoNode047_eval,poleRhoNode048_eval]
  simpa only [poleRhoNode049Coeff0,poleRhoNode049Coeff1,poleRhoNode049Coeff2,poleRhoNode049Coeff3,poleRhoNode049Coeff4,poleRhoNode049Coeff5,poleRhoNode049Coeff6,poleRhoNode049Coeff7,poleRhoNode049Coeff8,poleRhoNode049Coeff9,poleRhoNode049Coeff10,poleRhoNode049Coeff11,poleRhoNode049Coeff12] using
    pole_rho_mul_2_10 rho (poleRhoNode047Coeff0 a f) (poleRhoNode047Coeff1 a f) (poleRhoNode047Coeff2 a f) (poleRhoNode048Coeff0 a f) (poleRhoNode048Coeff1 a f) (poleRhoNode048Coeff2 a f) (poleRhoNode048Coeff3 a f) (poleRhoNode048Coeff4 a f) (poleRhoNode048Coeff5 a f) (poleRhoNode048Coeff6 a f) (poleRhoNode048Coeff7 a f) (poleRhoNode048Coeff8 a f) (poleRhoNode048Coeff9 a f) (poleRhoNode048Coeff10 a f)

theorem poleRhoScalar03_eval (a f rho : ℝ) :
    poleRhoScalar03 a f rho=(poleRhoScalar03Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar03 poleRhoScalar03Coeff0
  ring

theorem poleRhoNode051_eval (a f rho : ℝ) :
    poleRhoNode051 a f rho=(((poleRhoNode051Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode051Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode051Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode051Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode051
  rw [poleRhoNode046_eval,poleRhoBase_eval]
  simpa only [poleRhoNode051Coeff0,poleRhoNode051Coeff1,poleRhoNode051Coeff2,poleRhoNode051Coeff3] using
    pole_rho_mul_2_1 rho (poleRhoNode046Coeff0 a f) (poleRhoNode046Coeff1 a f) (poleRhoNode046Coeff2 a f) (poleRhoBaseCoeff0 a f) (poleRhoBaseCoeff1 a f)

theorem poleRhoNode052_eval (a f rho : ℝ) :
    poleRhoNode052 a f rho=(((poleRhoNode052Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode052Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode052Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode052Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode052
  rw [poleRhoScalar03_eval,poleRhoNode051_eval]
  simpa only [poleRhoNode052Coeff0,poleRhoNode052Coeff1,poleRhoNode052Coeff2,poleRhoNode052Coeff3] using
    pole_rho_mul_0_3 rho (poleRhoScalar03Coeff0 a f) (poleRhoNode051Coeff0 a f) (poleRhoNode051Coeff1 a f) (poleRhoNode051Coeff2 a f) (poleRhoNode051Coeff3 a f)

theorem poleRhoNode053_eval (a f rho : ℝ) :
    poleRhoNode053 a f rho=((((poleRhoNode053Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode053Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode053Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode053Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode053Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode053Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode053Coeff6 a f)*(rho)^(6 : ℕ))+((poleRhoNode053Coeff7 a f)*(rho)^(7 : ℕ)+((poleRhoNode053Coeff8 a f)*(rho)^(8 : ℕ)+(poleRhoNode053Coeff9 a f)*(rho)^(9 : ℕ))))) := by
  unfold poleRhoNode053
  rw [poleRhoNode034_eval,poleRhoRaw3_eval]
  simpa only [poleRhoNode053Coeff0,poleRhoNode053Coeff1,poleRhoNode053Coeff2,poleRhoNode053Coeff3,poleRhoNode053Coeff4,poleRhoNode053Coeff5,poleRhoNode053Coeff6,poleRhoNode053Coeff7,poleRhoNode053Coeff8,poleRhoNode053Coeff9] using
    pole_rho_mul_3_6 rho (poleRhoNode034Coeff0 a f) (poleRhoNode034Coeff1 a f) (poleRhoNode034Coeff2 a f) (poleRhoNode034Coeff3 a f) (poleRhoRaw3Coeff0 a f) (poleRhoRaw3Coeff1 a f) (poleRhoRaw3Coeff2 a f) (poleRhoRaw3Coeff3 a f) (poleRhoRaw3Coeff4 a f) (poleRhoRaw3Coeff5 a f) (poleRhoRaw3Coeff6 a f)

theorem poleRhoNode054_eval (a f rho : ℝ) :
    poleRhoNode054 a f rho=((((poleRhoNode054Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode054Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode054Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode054Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode054Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode054Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode054Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode054Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode054Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode054Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode054Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode054Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode054Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode054
  rw [poleRhoNode052_eval,poleRhoNode053_eval]
  simpa only [poleRhoNode054Coeff0,poleRhoNode054Coeff1,poleRhoNode054Coeff2,poleRhoNode054Coeff3,poleRhoNode054Coeff4,poleRhoNode054Coeff5,poleRhoNode054Coeff6,poleRhoNode054Coeff7,poleRhoNode054Coeff8,poleRhoNode054Coeff9,poleRhoNode054Coeff10,poleRhoNode054Coeff11,poleRhoNode054Coeff12] using
    pole_rho_mul_3_9 rho (poleRhoNode052Coeff0 a f) (poleRhoNode052Coeff1 a f) (poleRhoNode052Coeff2 a f) (poleRhoNode052Coeff3 a f) (poleRhoNode053Coeff0 a f) (poleRhoNode053Coeff1 a f) (poleRhoNode053Coeff2 a f) (poleRhoNode053Coeff3 a f) (poleRhoNode053Coeff4 a f) (poleRhoNode053Coeff5 a f) (poleRhoNode053Coeff6 a f) (poleRhoNode053Coeff7 a f) (poleRhoNode053Coeff8 a f) (poleRhoNode053Coeff9 a f)

theorem poleRhoScalar04_eval (a f rho : ℝ) :
    poleRhoScalar04 a f rho=(poleRhoScalar04Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar04 poleRhoScalar04Coeff0
  ring

theorem poleRhoNode056_eval (a f rho : ℝ) :
    poleRhoNode056 a f rho=(((poleRhoNode056Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode056Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode056Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode056Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode056Coeff4 a f)*(rho)^(4 : ℕ)))) := by
  unfold poleRhoNode056
  rw [poleRhoNode046_eval]
  simpa only [poleRhoNode056Coeff0,poleRhoNode056Coeff1,poleRhoNode056Coeff2,poleRhoNode056Coeff3,poleRhoNode056Coeff4] using
    pole_rho_mul_2_2 rho (poleRhoNode046Coeff0 a f) (poleRhoNode046Coeff1 a f) (poleRhoNode046Coeff2 a f) (poleRhoNode046Coeff0 a f) (poleRhoNode046Coeff1 a f) (poleRhoNode046Coeff2 a f)

theorem poleRhoNode057_eval (a f rho : ℝ) :
    poleRhoNode057 a f rho=(((poleRhoNode057Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode057Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode057Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode057Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode057Coeff4 a f)*(rho)^(4 : ℕ)))) := by
  unfold poleRhoNode057
  rw [poleRhoScalar04_eval,poleRhoNode056_eval]
  simpa only [poleRhoNode057Coeff0,poleRhoNode057Coeff1,poleRhoNode057Coeff2,poleRhoNode057Coeff3,poleRhoNode057Coeff4] using
    pole_rho_mul_0_4 rho (poleRhoScalar04Coeff0 a f) (poleRhoNode056Coeff0 a f) (poleRhoNode056Coeff1 a f) (poleRhoNode056Coeff2 a f) (poleRhoNode056Coeff3 a f) (poleRhoNode056Coeff4 a f)

theorem poleRhoNode058_eval (a f rho : ℝ) :
    poleRhoNode058 a f rho=((((poleRhoNode058Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode058Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode058Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode058Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode058Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode058Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode058Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode058Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode058Coeff8 a f)*(rho)^(8 : ℕ))))) := by
  unfold poleRhoNode058
  rw [poleRhoNode033_eval,poleRhoRaw4_eval]
  simpa only [poleRhoNode058Coeff0,poleRhoNode058Coeff1,poleRhoNode058Coeff2,poleRhoNode058Coeff3,poleRhoNode058Coeff4,poleRhoNode058Coeff5,poleRhoNode058Coeff6,poleRhoNode058Coeff7,poleRhoNode058Coeff8] using
    pole_rho_mul_2_6 rho (poleRhoNode033Coeff0 a f) (poleRhoNode033Coeff1 a f) (poleRhoNode033Coeff2 a f) (poleRhoRaw4Coeff0 a f) (poleRhoRaw4Coeff1 a f) (poleRhoRaw4Coeff2 a f) (poleRhoRaw4Coeff3 a f) (poleRhoRaw4Coeff4 a f) (poleRhoRaw4Coeff5 a f) (poleRhoRaw4Coeff6 a f)

theorem poleRhoNode059_eval (a f rho : ℝ) :
    poleRhoNode059 a f rho=((((poleRhoNode059Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode059Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode059Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode059Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode059Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode059Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode059Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode059Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode059Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode059Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode059Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode059Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode059Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode059
  rw [poleRhoNode057_eval,poleRhoNode058_eval]
  simpa only [poleRhoNode059Coeff0,poleRhoNode059Coeff1,poleRhoNode059Coeff2,poleRhoNode059Coeff3,poleRhoNode059Coeff4,poleRhoNode059Coeff5,poleRhoNode059Coeff6,poleRhoNode059Coeff7,poleRhoNode059Coeff8,poleRhoNode059Coeff9,poleRhoNode059Coeff10,poleRhoNode059Coeff11,poleRhoNode059Coeff12] using
    pole_rho_mul_4_8 rho (poleRhoNode057Coeff0 a f) (poleRhoNode057Coeff1 a f) (poleRhoNode057Coeff2 a f) (poleRhoNode057Coeff3 a f) (poleRhoNode057Coeff4 a f) (poleRhoNode058Coeff0 a f) (poleRhoNode058Coeff1 a f) (poleRhoNode058Coeff2 a f) (poleRhoNode058Coeff3 a f) (poleRhoNode058Coeff4 a f) (poleRhoNode058Coeff5 a f) (poleRhoNode058Coeff6 a f) (poleRhoNode058Coeff7 a f) (poleRhoNode058Coeff8 a f)

theorem poleRhoScalar05_eval (a f rho : ℝ) :
    poleRhoScalar05 a f rho=(poleRhoScalar05Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar05 poleRhoScalar05Coeff0
  ring

theorem poleRhoNode061_eval (a f rho : ℝ) :
    poleRhoNode061 a f rho=(((poleRhoNode061Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode061Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode061Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode061Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode061Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode061Coeff5 a f)*(rho)^(5 : ℕ)))) := by
  unfold poleRhoNode061
  rw [poleRhoNode056_eval,poleRhoBase_eval]
  simpa only [poleRhoNode061Coeff0,poleRhoNode061Coeff1,poleRhoNode061Coeff2,poleRhoNode061Coeff3,poleRhoNode061Coeff4,poleRhoNode061Coeff5] using
    pole_rho_mul_4_1 rho (poleRhoNode056Coeff0 a f) (poleRhoNode056Coeff1 a f) (poleRhoNode056Coeff2 a f) (poleRhoNode056Coeff3 a f) (poleRhoNode056Coeff4 a f) (poleRhoBaseCoeff0 a f) (poleRhoBaseCoeff1 a f)

theorem poleRhoNode062_eval (a f rho : ℝ) :
    poleRhoNode062 a f rho=(((poleRhoNode062Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode062Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode062Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode062Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode062Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode062Coeff5 a f)*(rho)^(5 : ℕ)))) := by
  unfold poleRhoNode062
  rw [poleRhoScalar05_eval,poleRhoNode061_eval]
  simpa only [poleRhoNode062Coeff0,poleRhoNode062Coeff1,poleRhoNode062Coeff2,poleRhoNode062Coeff3,poleRhoNode062Coeff4,poleRhoNode062Coeff5] using
    pole_rho_mul_0_5 rho (poleRhoScalar05Coeff0 a f) (poleRhoNode061Coeff0 a f) (poleRhoNode061Coeff1 a f) (poleRhoNode061Coeff2 a f) (poleRhoNode061Coeff3 a f) (poleRhoNode061Coeff4 a f) (poleRhoNode061Coeff5 a f)

theorem poleRhoNode063_eval (a f rho : ℝ) :
    poleRhoNode063 a f rho=((((poleRhoNode063Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode063Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode063Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode063Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode063Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode063Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode063Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode063Coeff7 a f)*(rho)^(7 : ℕ)))) := by
  unfold poleRhoNode063
  rw [poleRhoC_eval,poleRhoRaw5_eval]
  simpa only [poleRhoNode063Coeff0,poleRhoNode063Coeff1,poleRhoNode063Coeff2,poleRhoNode063Coeff3,poleRhoNode063Coeff4,poleRhoNode063Coeff5,poleRhoNode063Coeff6,poleRhoNode063Coeff7] using
    pole_rho_mul_1_6 rho (poleRhoCCoeff0 a f) (poleRhoCCoeff1 a f) (poleRhoRaw5Coeff0 a f) (poleRhoRaw5Coeff1 a f) (poleRhoRaw5Coeff2 a f) (poleRhoRaw5Coeff3 a f) (poleRhoRaw5Coeff4 a f) (poleRhoRaw5Coeff5 a f) (poleRhoRaw5Coeff6 a f)

theorem poleRhoNode064_eval (a f rho : ℝ) :
    poleRhoNode064 a f rho=((((poleRhoNode064Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode064Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode064Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode064Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode064Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode064Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode064Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode064Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode064Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode064Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode064Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode064Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode064Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode064
  rw [poleRhoNode062_eval,poleRhoNode063_eval]
  simpa only [poleRhoNode064Coeff0,poleRhoNode064Coeff1,poleRhoNode064Coeff2,poleRhoNode064Coeff3,poleRhoNode064Coeff4,poleRhoNode064Coeff5,poleRhoNode064Coeff6,poleRhoNode064Coeff7,poleRhoNode064Coeff8,poleRhoNode064Coeff9,poleRhoNode064Coeff10,poleRhoNode064Coeff11,poleRhoNode064Coeff12] using
    pole_rho_mul_5_7 rho (poleRhoNode062Coeff0 a f) (poleRhoNode062Coeff1 a f) (poleRhoNode062Coeff2 a f) (poleRhoNode062Coeff3 a f) (poleRhoNode062Coeff4 a f) (poleRhoNode062Coeff5 a f) (poleRhoNode063Coeff0 a f) (poleRhoNode063Coeff1 a f) (poleRhoNode063Coeff2 a f) (poleRhoNode063Coeff3 a f) (poleRhoNode063Coeff4 a f) (poleRhoNode063Coeff5 a f) (poleRhoNode063Coeff6 a f) (poleRhoNode063Coeff7 a f)

theorem poleRhoScalar06_eval (a f rho : ℝ) :
    poleRhoScalar06 a f rho=(poleRhoScalar06Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar06 poleRhoScalar06Coeff0
  ring

theorem poleRhoNode066_eval (a f rho : ℝ) :
    poleRhoNode066 a f rho=(((poleRhoNode066Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode066Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode066Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoNode066Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode066Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoNode066Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode066Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoNode066
  rw [poleRhoNode051_eval]
  simpa only [poleRhoNode066Coeff0,poleRhoNode066Coeff1,poleRhoNode066Coeff2,poleRhoNode066Coeff3,poleRhoNode066Coeff4,poleRhoNode066Coeff5,poleRhoNode066Coeff6] using
    pole_rho_mul_3_3 rho (poleRhoNode051Coeff0 a f) (poleRhoNode051Coeff1 a f) (poleRhoNode051Coeff2 a f) (poleRhoNode051Coeff3 a f) (poleRhoNode051Coeff0 a f) (poleRhoNode051Coeff1 a f) (poleRhoNode051Coeff2 a f) (poleRhoNode051Coeff3 a f)

theorem poleRhoNode067_eval (a f rho : ℝ) :
    poleRhoNode067 a f rho=(((poleRhoNode067Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode067Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode067Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoNode067Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode067Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoNode067Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode067Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoNode067
  rw [poleRhoScalar06_eval,poleRhoNode066_eval]
  simpa only [poleRhoNode067Coeff0,poleRhoNode067Coeff1,poleRhoNode067Coeff2,poleRhoNode067Coeff3,poleRhoNode067Coeff4,poleRhoNode067Coeff5,poleRhoNode067Coeff6] using
    pole_rho_mul_0_6 rho (poleRhoScalar06Coeff0 a f) (poleRhoNode066Coeff0 a f) (poleRhoNode066Coeff1 a f) (poleRhoNode066Coeff2 a f) (poleRhoNode066Coeff3 a f) (poleRhoNode066Coeff4 a f) (poleRhoNode066Coeff5 a f) (poleRhoNode066Coeff6 a f)

theorem poleRhoNode068_eval (a f rho : ℝ) :
    poleRhoNode068 a f rho=(((poleRhoNode068Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode068Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode068Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoNode068Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode068Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoNode068Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode068Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoNode068
  rw [poleRhoOne_eval,poleRhoRaw6_eval]
  simpa only [poleRhoNode068Coeff0,poleRhoNode068Coeff1,poleRhoNode068Coeff2,poleRhoNode068Coeff3,poleRhoNode068Coeff4,poleRhoNode068Coeff5,poleRhoNode068Coeff6] using
    pole_rho_mul_0_6 rho (poleRhoOneCoeff0 a f) (poleRhoRaw6Coeff0 a f) (poleRhoRaw6Coeff1 a f) (poleRhoRaw6Coeff2 a f) (poleRhoRaw6Coeff3 a f) (poleRhoRaw6Coeff4 a f) (poleRhoRaw6Coeff5 a f) (poleRhoRaw6Coeff6 a f)

theorem poleRhoNode069_eval (a f rho : ℝ) :
    poleRhoNode069 a f rho=((((poleRhoNode069Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode069Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode069Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode069Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode069Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode069Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode069Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode069Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode069Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode069Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode069Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode069Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode069Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode069
  rw [poleRhoNode067_eval,poleRhoNode068_eval]
  simpa only [poleRhoNode069Coeff0,poleRhoNode069Coeff1,poleRhoNode069Coeff2,poleRhoNode069Coeff3,poleRhoNode069Coeff4,poleRhoNode069Coeff5,poleRhoNode069Coeff6,poleRhoNode069Coeff7,poleRhoNode069Coeff8,poleRhoNode069Coeff9,poleRhoNode069Coeff10,poleRhoNode069Coeff11,poleRhoNode069Coeff12] using
    pole_rho_mul_6_6 rho (poleRhoNode067Coeff0 a f) (poleRhoNode067Coeff1 a f) (poleRhoNode067Coeff2 a f) (poleRhoNode067Coeff3 a f) (poleRhoNode067Coeff4 a f) (poleRhoNode067Coeff5 a f) (poleRhoNode067Coeff6 a f) (poleRhoNode068Coeff0 a f) (poleRhoNode068Coeff1 a f) (poleRhoNode068Coeff2 a f) (poleRhoNode068Coeff3 a f) (poleRhoNode068Coeff4 a f) (poleRhoNode068Coeff5 a f) (poleRhoNode068Coeff6 a f)

theorem poleRhoNode070_eval (a f rho : ℝ) :
    poleRhoNode070 a f rho=((((poleRhoNode070Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode070Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode070Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode070Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode070Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode070Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode070Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode070Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode070Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode070Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode070Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode070Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode070Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode070
  rw [poleRhoNode044_eval,poleRhoNode049_eval]
  simpa only [poleRhoNode070Coeff0,poleRhoNode070Coeff1,poleRhoNode070Coeff2,poleRhoNode070Coeff3,poleRhoNode070Coeff4,poleRhoNode070Coeff5,poleRhoNode070Coeff6,poleRhoNode070Coeff7,poleRhoNode070Coeff8,poleRhoNode070Coeff9,poleRhoNode070Coeff10,poleRhoNode070Coeff11,poleRhoNode070Coeff12] using
    pole_rho_add_12_12 rho (poleRhoNode044Coeff0 a f) (poleRhoNode044Coeff1 a f) (poleRhoNode044Coeff2 a f) (poleRhoNode044Coeff3 a f) (poleRhoNode044Coeff4 a f) (poleRhoNode044Coeff5 a f) (poleRhoNode044Coeff6 a f) (poleRhoNode044Coeff7 a f) (poleRhoNode044Coeff8 a f) (poleRhoNode044Coeff9 a f) (poleRhoNode044Coeff10 a f) (poleRhoNode044Coeff11 a f) (poleRhoNode044Coeff12 a f) (poleRhoNode049Coeff0 a f) (poleRhoNode049Coeff1 a f) (poleRhoNode049Coeff2 a f) (poleRhoNode049Coeff3 a f) (poleRhoNode049Coeff4 a f) (poleRhoNode049Coeff5 a f) (poleRhoNode049Coeff6 a f) (poleRhoNode049Coeff7 a f) (poleRhoNode049Coeff8 a f) (poleRhoNode049Coeff9 a f) (poleRhoNode049Coeff10 a f) (poleRhoNode049Coeff11 a f) (poleRhoNode049Coeff12 a f)

theorem poleRhoNode071_eval (a f rho : ℝ) :
    poleRhoNode071 a f rho=((((poleRhoNode071Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode071Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode071Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode071Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode071Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode071Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode071Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode071Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode071Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode071Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode071Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode071Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode071Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode071
  rw [poleRhoNode038_eval,poleRhoNode070_eval]
  simpa only [poleRhoNode071Coeff0,poleRhoNode071Coeff1,poleRhoNode071Coeff2,poleRhoNode071Coeff3,poleRhoNode071Coeff4,poleRhoNode071Coeff5,poleRhoNode071Coeff6,poleRhoNode071Coeff7,poleRhoNode071Coeff8,poleRhoNode071Coeff9,poleRhoNode071Coeff10,poleRhoNode071Coeff11,poleRhoNode071Coeff12] using
    pole_rho_add_12_12 rho (poleRhoNode038Coeff0 a f) (poleRhoNode038Coeff1 a f) (poleRhoNode038Coeff2 a f) (poleRhoNode038Coeff3 a f) (poleRhoNode038Coeff4 a f) (poleRhoNode038Coeff5 a f) (poleRhoNode038Coeff6 a f) (poleRhoNode038Coeff7 a f) (poleRhoNode038Coeff8 a f) (poleRhoNode038Coeff9 a f) (poleRhoNode038Coeff10 a f) (poleRhoNode038Coeff11 a f) (poleRhoNode038Coeff12 a f) (poleRhoNode070Coeff0 a f) (poleRhoNode070Coeff1 a f) (poleRhoNode070Coeff2 a f) (poleRhoNode070Coeff3 a f) (poleRhoNode070Coeff4 a f) (poleRhoNode070Coeff5 a f) (poleRhoNode070Coeff6 a f) (poleRhoNode070Coeff7 a f) (poleRhoNode070Coeff8 a f) (poleRhoNode070Coeff9 a f) (poleRhoNode070Coeff10 a f) (poleRhoNode070Coeff11 a f) (poleRhoNode070Coeff12 a f)

theorem poleRhoNode072_eval (a f rho : ℝ) :
    poleRhoNode072 a f rho=((((poleRhoNode072Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode072Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode072Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode072Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode072Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode072Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode072Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode072Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode072Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode072Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode072Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode072Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode072Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode072
  rw [poleRhoNode054_eval,poleRhoNode059_eval]
  simpa only [poleRhoNode072Coeff0,poleRhoNode072Coeff1,poleRhoNode072Coeff2,poleRhoNode072Coeff3,poleRhoNode072Coeff4,poleRhoNode072Coeff5,poleRhoNode072Coeff6,poleRhoNode072Coeff7,poleRhoNode072Coeff8,poleRhoNode072Coeff9,poleRhoNode072Coeff10,poleRhoNode072Coeff11,poleRhoNode072Coeff12] using
    pole_rho_add_12_12 rho (poleRhoNode054Coeff0 a f) (poleRhoNode054Coeff1 a f) (poleRhoNode054Coeff2 a f) (poleRhoNode054Coeff3 a f) (poleRhoNode054Coeff4 a f) (poleRhoNode054Coeff5 a f) (poleRhoNode054Coeff6 a f) (poleRhoNode054Coeff7 a f) (poleRhoNode054Coeff8 a f) (poleRhoNode054Coeff9 a f) (poleRhoNode054Coeff10 a f) (poleRhoNode054Coeff11 a f) (poleRhoNode054Coeff12 a f) (poleRhoNode059Coeff0 a f) (poleRhoNode059Coeff1 a f) (poleRhoNode059Coeff2 a f) (poleRhoNode059Coeff3 a f) (poleRhoNode059Coeff4 a f) (poleRhoNode059Coeff5 a f) (poleRhoNode059Coeff6 a f) (poleRhoNode059Coeff7 a f) (poleRhoNode059Coeff8 a f) (poleRhoNode059Coeff9 a f) (poleRhoNode059Coeff10 a f) (poleRhoNode059Coeff11 a f) (poleRhoNode059Coeff12 a f)

theorem poleRhoNode073_eval (a f rho : ℝ) :
    poleRhoNode073 a f rho=((((poleRhoNode073Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode073Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode073Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode073Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode073Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode073Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode073Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode073Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode073Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode073Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode073Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode073Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode073Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode073
  rw [poleRhoNode064_eval,poleRhoNode069_eval]
  simpa only [poleRhoNode073Coeff0,poleRhoNode073Coeff1,poleRhoNode073Coeff2,poleRhoNode073Coeff3,poleRhoNode073Coeff4,poleRhoNode073Coeff5,poleRhoNode073Coeff6,poleRhoNode073Coeff7,poleRhoNode073Coeff8,poleRhoNode073Coeff9,poleRhoNode073Coeff10,poleRhoNode073Coeff11,poleRhoNode073Coeff12] using
    pole_rho_add_12_12 rho (poleRhoNode064Coeff0 a f) (poleRhoNode064Coeff1 a f) (poleRhoNode064Coeff2 a f) (poleRhoNode064Coeff3 a f) (poleRhoNode064Coeff4 a f) (poleRhoNode064Coeff5 a f) (poleRhoNode064Coeff6 a f) (poleRhoNode064Coeff7 a f) (poleRhoNode064Coeff8 a f) (poleRhoNode064Coeff9 a f) (poleRhoNode064Coeff10 a f) (poleRhoNode064Coeff11 a f) (poleRhoNode064Coeff12 a f) (poleRhoNode069Coeff0 a f) (poleRhoNode069Coeff1 a f) (poleRhoNode069Coeff2 a f) (poleRhoNode069Coeff3 a f) (poleRhoNode069Coeff4 a f) (poleRhoNode069Coeff5 a f) (poleRhoNode069Coeff6 a f) (poleRhoNode069Coeff7 a f) (poleRhoNode069Coeff8 a f) (poleRhoNode069Coeff9 a f) (poleRhoNode069Coeff10 a f) (poleRhoNode069Coeff11 a f) (poleRhoNode069Coeff12 a f)

theorem poleRhoNode074_eval (a f rho : ℝ) :
    poleRhoNode074 a f rho=((((poleRhoNode074Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode074Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode074Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode074Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode074Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode074Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode074Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode074Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode074Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode074Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode074Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode074Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode074Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode074
  rw [poleRhoNode072_eval,poleRhoNode073_eval]
  simpa only [poleRhoNode074Coeff0,poleRhoNode074Coeff1,poleRhoNode074Coeff2,poleRhoNode074Coeff3,poleRhoNode074Coeff4,poleRhoNode074Coeff5,poleRhoNode074Coeff6,poleRhoNode074Coeff7,poleRhoNode074Coeff8,poleRhoNode074Coeff9,poleRhoNode074Coeff10,poleRhoNode074Coeff11,poleRhoNode074Coeff12] using
    pole_rho_add_12_12 rho (poleRhoNode072Coeff0 a f) (poleRhoNode072Coeff1 a f) (poleRhoNode072Coeff2 a f) (poleRhoNode072Coeff3 a f) (poleRhoNode072Coeff4 a f) (poleRhoNode072Coeff5 a f) (poleRhoNode072Coeff6 a f) (poleRhoNode072Coeff7 a f) (poleRhoNode072Coeff8 a f) (poleRhoNode072Coeff9 a f) (poleRhoNode072Coeff10 a f) (poleRhoNode072Coeff11 a f) (poleRhoNode072Coeff12 a f) (poleRhoNode073Coeff0 a f) (poleRhoNode073Coeff1 a f) (poleRhoNode073Coeff2 a f) (poleRhoNode073Coeff3 a f) (poleRhoNode073Coeff4 a f) (poleRhoNode073Coeff5 a f) (poleRhoNode073Coeff6 a f) (poleRhoNode073Coeff7 a f) (poleRhoNode073Coeff8 a f) (poleRhoNode073Coeff9 a f) (poleRhoNode073Coeff10 a f) (poleRhoNode073Coeff11 a f) (poleRhoNode073Coeff12 a f)

theorem poleRhoNode075_eval (a f rho : ℝ) :
    poleRhoNode075 a f rho=((((poleRhoNode075Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode075Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode075Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode075Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode075Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode075Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode075Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode075Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode075Coeff8 a f)*(rho)^(8 : ℕ)))+(((poleRhoNode075Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode075Coeff10 a f)*(rho)^(10 : ℕ))+((poleRhoNode075Coeff11 a f)*(rho)^(11 : ℕ)+(poleRhoNode075Coeff12 a f)*(rho)^(12 : ℕ))))) := by
  unfold poleRhoNode075
  rw [poleRhoNode071_eval,poleRhoNode074_eval]
  simpa only [poleRhoNode075Coeff0,poleRhoNode075Coeff1,poleRhoNode075Coeff2,poleRhoNode075Coeff3,poleRhoNode075Coeff4,poleRhoNode075Coeff5,poleRhoNode075Coeff6,poleRhoNode075Coeff7,poleRhoNode075Coeff8,poleRhoNode075Coeff9,poleRhoNode075Coeff10,poleRhoNode075Coeff11,poleRhoNode075Coeff12] using
    pole_rho_add_12_12 rho (poleRhoNode071Coeff0 a f) (poleRhoNode071Coeff1 a f) (poleRhoNode071Coeff2 a f) (poleRhoNode071Coeff3 a f) (poleRhoNode071Coeff4 a f) (poleRhoNode071Coeff5 a f) (poleRhoNode071Coeff6 a f) (poleRhoNode071Coeff7 a f) (poleRhoNode071Coeff8 a f) (poleRhoNode071Coeff9 a f) (poleRhoNode071Coeff10 a f) (poleRhoNode071Coeff11 a f) (poleRhoNode071Coeff12 a f) (poleRhoNode074Coeff0 a f) (poleRhoNode074Coeff1 a f) (poleRhoNode074Coeff2 a f) (poleRhoNode074Coeff3 a f) (poleRhoNode074Coeff4 a f) (poleRhoNode074Coeff5 a f) (poleRhoNode074Coeff6 a f) (poleRhoNode074Coeff7 a f) (poleRhoNode074Coeff8 a f) (poleRhoNode074Coeff9 a f) (poleRhoNode074Coeff10 a f) (poleRhoNode074Coeff11 a f) (poleRhoNode074Coeff12 a f)

theorem poleRhoInvariant1_eval (a f rho : ℝ) :
    poleRhoInvariant1 a f rho=(poleRhoInvariant1Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoInvariant1 poleRhoInvariant1Coeff0
  ring

theorem poleRhoNode077_eval (a f rho : ℝ) :
    poleRhoNode077 a f rho=(((poleRhoNode077Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode077Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode077Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode077Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode077
  rw [poleRhoNode025_eval,poleRhoS_eval]
  simpa only [poleRhoNode077Coeff0,poleRhoNode077Coeff1,poleRhoNode077Coeff2,poleRhoNode077Coeff3] using
    pole_rho_mul_2_1 rho (poleRhoNode025Coeff0 a f) (poleRhoNode025Coeff1 a f) (poleRhoNode025Coeff2 a f) (poleRhoSCoeff0 a f) (poleRhoSCoeff1 a f)

theorem poleRhoNode078_eval (a f rho : ℝ) :
    poleRhoNode078 a f rho=(((poleRhoNode078Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode078Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode078Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode078Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode078
  rw [poleRhoInvariant1_eval,poleRhoNode022_eval]
  simpa only [poleRhoNode078Coeff0,poleRhoNode078Coeff1,poleRhoNode078Coeff2,poleRhoNode078Coeff3] using
    pole_rho_mul_0_3 rho (poleRhoInvariant1Coeff0 a f) (poleRhoNode022Coeff0 a f) (poleRhoNode022Coeff1 a f) (poleRhoNode022Coeff2 a f) (poleRhoNode022Coeff3 a f)

theorem poleRhoNode079_eval (a f rho : ℝ) :
    poleRhoNode079 a f rho=(((poleRhoNode079Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode079Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode079Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoNode079Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode079Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoNode079Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode079Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoNode079
  rw [poleRhoNode077_eval,poleRhoUpper1_eval]
  simpa only [poleRhoNode079Coeff0,poleRhoNode079Coeff1,poleRhoNode079Coeff2,poleRhoNode079Coeff3,poleRhoNode079Coeff4,poleRhoNode079Coeff5,poleRhoNode079Coeff6] using
    pole_rho_mul_3_3 rho (poleRhoNode077Coeff0 a f) (poleRhoNode077Coeff1 a f) (poleRhoNode077Coeff2 a f) (poleRhoNode077Coeff3 a f) (poleRhoUpper1Coeff0 a f) (poleRhoUpper1Coeff1 a f) (poleRhoUpper1Coeff2 a f) (poleRhoUpper1Coeff3 a f)

theorem poleRhoNode080_eval (a f rho : ℝ) :
    poleRhoNode080 a f rho=((((poleRhoNode080Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode080Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode080Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode080Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode080Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode080Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode080Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode080Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode080Coeff8 a f)*(rho)^(8 : ℕ))))) := by
  unfold poleRhoNode080
  rw [poleRhoNode023_eval,poleRhoNode079_eval]
  simpa only [poleRhoNode080Coeff0,poleRhoNode080Coeff1,poleRhoNode080Coeff2,poleRhoNode080Coeff3,poleRhoNode080Coeff4,poleRhoNode080Coeff5,poleRhoNode080Coeff6,poleRhoNode080Coeff7,poleRhoNode080Coeff8] using
    pole_rho_mul_2_6 rho (poleRhoNode023Coeff0 a f) (poleRhoNode023Coeff1 a f) (poleRhoNode023Coeff2 a f) (poleRhoNode079Coeff0 a f) (poleRhoNode079Coeff1 a f) (poleRhoNode079Coeff2 a f) (poleRhoNode079Coeff3 a f) (poleRhoNode079Coeff4 a f) (poleRhoNode079Coeff5 a f) (poleRhoNode079Coeff6 a f)

theorem poleRhoNode081_eval (a f rho : ℝ) :
    poleRhoNode081 a f rho=((((poleRhoNode081Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode081Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode081Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode081Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode081Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode081Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode081Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode081Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode081Coeff8 a f)*(rho)^(8 : ℕ)))+((poleRhoNode081Coeff9 a f)*(rho)^(9 : ℕ)+((poleRhoNode081Coeff10 a f)*(rho)^(10 : ℕ)+(poleRhoNode081Coeff11 a f)*(rho)^(11 : ℕ))))) := by
  unfold poleRhoNode081
  rw [poleRhoNode078_eval,poleRhoNode080_eval]
  simpa only [poleRhoNode081Coeff0,poleRhoNode081Coeff1,poleRhoNode081Coeff2,poleRhoNode081Coeff3,poleRhoNode081Coeff4,poleRhoNode081Coeff5,poleRhoNode081Coeff6,poleRhoNode081Coeff7,poleRhoNode081Coeff8,poleRhoNode081Coeff9,poleRhoNode081Coeff10,poleRhoNode081Coeff11] using
    pole_rho_mul_3_8 rho (poleRhoNode078Coeff0 a f) (poleRhoNode078Coeff1 a f) (poleRhoNode078Coeff2 a f) (poleRhoNode078Coeff3 a f) (poleRhoNode080Coeff0 a f) (poleRhoNode080Coeff1 a f) (poleRhoNode080Coeff2 a f) (poleRhoNode080Coeff3 a f) (poleRhoNode080Coeff4 a f) (poleRhoNode080Coeff5 a f) (poleRhoNode080Coeff6 a f) (poleRhoNode080Coeff7 a f) (poleRhoNode080Coeff8 a f)

theorem poleRhoScalar11_eval (a f rho : ℝ) :
    poleRhoScalar11 a f rho=(poleRhoScalar11Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar11 poleRhoScalar11Coeff0
  ring

theorem poleRhoNode083_eval (a f rho : ℝ) :
    poleRhoNode083 a f rho=(poleRhoNode083Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoNode083
  rw [poleRhoScalar11_eval,poleRhoOne_eval]
  simpa only [poleRhoNode083Coeff0] using
    pole_rho_mul_0_0 rho (poleRhoScalar11Coeff0 a f) (poleRhoOneCoeff0 a f)

theorem poleRhoNode084_eval (a f rho : ℝ) :
    poleRhoNode084 a f rho=((((poleRhoNode084Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode084Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode084Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode084Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode084Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode084Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode084Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode084Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode084Coeff8 a f)*(rho)^(8 : ℕ)))+((poleRhoNode084Coeff9 a f)*(rho)^(9 : ℕ)+((poleRhoNode084Coeff10 a f)*(rho)^(10 : ℕ)+(poleRhoNode084Coeff11 a f)*(rho)^(11 : ℕ))))) := by
  unfold poleRhoNode084
  rw [poleRhoNode083_eval,poleRhoNode043_eval]
  simpa only [poleRhoNode084Coeff0,poleRhoNode084Coeff1,poleRhoNode084Coeff2,poleRhoNode084Coeff3,poleRhoNode084Coeff4,poleRhoNode084Coeff5,poleRhoNode084Coeff6,poleRhoNode084Coeff7,poleRhoNode084Coeff8,poleRhoNode084Coeff9,poleRhoNode084Coeff10,poleRhoNode084Coeff11] using
    pole_rho_mul_0_11 rho (poleRhoNode083Coeff0 a f) (poleRhoNode043Coeff0 a f) (poleRhoNode043Coeff1 a f) (poleRhoNode043Coeff2 a f) (poleRhoNode043Coeff3 a f) (poleRhoNode043Coeff4 a f) (poleRhoNode043Coeff5 a f) (poleRhoNode043Coeff6 a f) (poleRhoNode043Coeff7 a f) (poleRhoNode043Coeff8 a f) (poleRhoNode043Coeff9 a f) (poleRhoNode043Coeff10 a f) (poleRhoNode043Coeff11 a f)

theorem poleRhoScalar12_eval (a f rho : ℝ) :
    poleRhoScalar12 a f rho=(poleRhoScalar12Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar12 poleRhoScalar12Coeff0
  ring

theorem poleRhoNode086_eval (a f rho : ℝ) :
    poleRhoNode086 a f rho=((poleRhoNode086Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode086Coeff1 a f)*(rho)^(1 : ℕ)) := by
  unfold poleRhoNode086
  rw [poleRhoScalar12_eval,poleRhoBase_eval]
  simpa only [poleRhoNode086Coeff0,poleRhoNode086Coeff1] using
    pole_rho_mul_0_1 rho (poleRhoScalar12Coeff0 a f) (poleRhoBaseCoeff0 a f) (poleRhoBaseCoeff1 a f)

theorem poleRhoNode087_eval (a f rho : ℝ) :
    poleRhoNode087 a f rho=((((poleRhoNode087Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode087Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode087Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode087Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode087Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode087Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode087Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode087Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode087Coeff8 a f)*(rho)^(8 : ℕ)))+((poleRhoNode087Coeff9 a f)*(rho)^(9 : ℕ)+((poleRhoNode087Coeff10 a f)*(rho)^(10 : ℕ)+(poleRhoNode087Coeff11 a f)*(rho)^(11 : ℕ))))) := by
  unfold poleRhoNode087
  rw [poleRhoNode086_eval,poleRhoNode048_eval]
  simpa only [poleRhoNode087Coeff0,poleRhoNode087Coeff1,poleRhoNode087Coeff2,poleRhoNode087Coeff3,poleRhoNode087Coeff4,poleRhoNode087Coeff5,poleRhoNode087Coeff6,poleRhoNode087Coeff7,poleRhoNode087Coeff8,poleRhoNode087Coeff9,poleRhoNode087Coeff10,poleRhoNode087Coeff11] using
    pole_rho_mul_1_10 rho (poleRhoNode086Coeff0 a f) (poleRhoNode086Coeff1 a f) (poleRhoNode048Coeff0 a f) (poleRhoNode048Coeff1 a f) (poleRhoNode048Coeff2 a f) (poleRhoNode048Coeff3 a f) (poleRhoNode048Coeff4 a f) (poleRhoNode048Coeff5 a f) (poleRhoNode048Coeff6 a f) (poleRhoNode048Coeff7 a f) (poleRhoNode048Coeff8 a f) (poleRhoNode048Coeff9 a f) (poleRhoNode048Coeff10 a f)

theorem poleRhoScalar13_eval (a f rho : ℝ) :
    poleRhoScalar13 a f rho=(poleRhoScalar13Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar13 poleRhoScalar13Coeff0
  ring

theorem poleRhoNode089_eval (a f rho : ℝ) :
    poleRhoNode089 a f rho=((poleRhoNode089Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode089Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode089Coeff2 a f)*(rho)^(2 : ℕ))) := by
  unfold poleRhoNode089
  rw [poleRhoScalar13_eval,poleRhoNode046_eval]
  simpa only [poleRhoNode089Coeff0,poleRhoNode089Coeff1,poleRhoNode089Coeff2] using
    pole_rho_mul_0_2 rho (poleRhoScalar13Coeff0 a f) (poleRhoNode046Coeff0 a f) (poleRhoNode046Coeff1 a f) (poleRhoNode046Coeff2 a f)

theorem poleRhoNode090_eval (a f rho : ℝ) :
    poleRhoNode090 a f rho=((((poleRhoNode090Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode090Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode090Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode090Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode090Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode090Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode090Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode090Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode090Coeff8 a f)*(rho)^(8 : ℕ)))+((poleRhoNode090Coeff9 a f)*(rho)^(9 : ℕ)+((poleRhoNode090Coeff10 a f)*(rho)^(10 : ℕ)+(poleRhoNode090Coeff11 a f)*(rho)^(11 : ℕ))))) := by
  unfold poleRhoNode090
  rw [poleRhoNode089_eval,poleRhoNode053_eval]
  simpa only [poleRhoNode090Coeff0,poleRhoNode090Coeff1,poleRhoNode090Coeff2,poleRhoNode090Coeff3,poleRhoNode090Coeff4,poleRhoNode090Coeff5,poleRhoNode090Coeff6,poleRhoNode090Coeff7,poleRhoNode090Coeff8,poleRhoNode090Coeff9,poleRhoNode090Coeff10,poleRhoNode090Coeff11] using
    pole_rho_mul_2_9 rho (poleRhoNode089Coeff0 a f) (poleRhoNode089Coeff1 a f) (poleRhoNode089Coeff2 a f) (poleRhoNode053Coeff0 a f) (poleRhoNode053Coeff1 a f) (poleRhoNode053Coeff2 a f) (poleRhoNode053Coeff3 a f) (poleRhoNode053Coeff4 a f) (poleRhoNode053Coeff5 a f) (poleRhoNode053Coeff6 a f) (poleRhoNode053Coeff7 a f) (poleRhoNode053Coeff8 a f) (poleRhoNode053Coeff9 a f)

theorem poleRhoScalar14_eval (a f rho : ℝ) :
    poleRhoScalar14 a f rho=(poleRhoScalar14Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar14 poleRhoScalar14Coeff0
  ring

theorem poleRhoNode092_eval (a f rho : ℝ) :
    poleRhoNode092 a f rho=(((poleRhoNode092Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode092Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode092Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode092Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode092
  rw [poleRhoScalar14_eval,poleRhoNode051_eval]
  simpa only [poleRhoNode092Coeff0,poleRhoNode092Coeff1,poleRhoNode092Coeff2,poleRhoNode092Coeff3] using
    pole_rho_mul_0_3 rho (poleRhoScalar14Coeff0 a f) (poleRhoNode051Coeff0 a f) (poleRhoNode051Coeff1 a f) (poleRhoNode051Coeff2 a f) (poleRhoNode051Coeff3 a f)

theorem poleRhoNode093_eval (a f rho : ℝ) :
    poleRhoNode093 a f rho=((((poleRhoNode093Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode093Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode093Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode093Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode093Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode093Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode093Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode093Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode093Coeff8 a f)*(rho)^(8 : ℕ)))+((poleRhoNode093Coeff9 a f)*(rho)^(9 : ℕ)+((poleRhoNode093Coeff10 a f)*(rho)^(10 : ℕ)+(poleRhoNode093Coeff11 a f)*(rho)^(11 : ℕ))))) := by
  unfold poleRhoNode093
  rw [poleRhoNode092_eval,poleRhoNode058_eval]
  simpa only [poleRhoNode093Coeff0,poleRhoNode093Coeff1,poleRhoNode093Coeff2,poleRhoNode093Coeff3,poleRhoNode093Coeff4,poleRhoNode093Coeff5,poleRhoNode093Coeff6,poleRhoNode093Coeff7,poleRhoNode093Coeff8,poleRhoNode093Coeff9,poleRhoNode093Coeff10,poleRhoNode093Coeff11] using
    pole_rho_mul_3_8 rho (poleRhoNode092Coeff0 a f) (poleRhoNode092Coeff1 a f) (poleRhoNode092Coeff2 a f) (poleRhoNode092Coeff3 a f) (poleRhoNode058Coeff0 a f) (poleRhoNode058Coeff1 a f) (poleRhoNode058Coeff2 a f) (poleRhoNode058Coeff3 a f) (poleRhoNode058Coeff4 a f) (poleRhoNode058Coeff5 a f) (poleRhoNode058Coeff6 a f) (poleRhoNode058Coeff7 a f) (poleRhoNode058Coeff8 a f)

theorem poleRhoScalar15_eval (a f rho : ℝ) :
    poleRhoScalar15 a f rho=(poleRhoScalar15Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar15 poleRhoScalar15Coeff0
  ring

theorem poleRhoNode095_eval (a f rho : ℝ) :
    poleRhoNode095 a f rho=(((poleRhoNode095Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode095Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode095Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode095Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode095Coeff4 a f)*(rho)^(4 : ℕ)))) := by
  unfold poleRhoNode095
  rw [poleRhoScalar15_eval,poleRhoNode056_eval]
  simpa only [poleRhoNode095Coeff0,poleRhoNode095Coeff1,poleRhoNode095Coeff2,poleRhoNode095Coeff3,poleRhoNode095Coeff4] using
    pole_rho_mul_0_4 rho (poleRhoScalar15Coeff0 a f) (poleRhoNode056Coeff0 a f) (poleRhoNode056Coeff1 a f) (poleRhoNode056Coeff2 a f) (poleRhoNode056Coeff3 a f) (poleRhoNode056Coeff4 a f)

theorem poleRhoNode096_eval (a f rho : ℝ) :
    poleRhoNode096 a f rho=((((poleRhoNode096Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode096Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode096Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode096Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode096Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode096Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode096Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode096Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode096Coeff8 a f)*(rho)^(8 : ℕ)))+((poleRhoNode096Coeff9 a f)*(rho)^(9 : ℕ)+((poleRhoNode096Coeff10 a f)*(rho)^(10 : ℕ)+(poleRhoNode096Coeff11 a f)*(rho)^(11 : ℕ))))) := by
  unfold poleRhoNode096
  rw [poleRhoNode095_eval,poleRhoNode063_eval]
  simpa only [poleRhoNode096Coeff0,poleRhoNode096Coeff1,poleRhoNode096Coeff2,poleRhoNode096Coeff3,poleRhoNode096Coeff4,poleRhoNode096Coeff5,poleRhoNode096Coeff6,poleRhoNode096Coeff7,poleRhoNode096Coeff8,poleRhoNode096Coeff9,poleRhoNode096Coeff10,poleRhoNode096Coeff11] using
    pole_rho_mul_4_7 rho (poleRhoNode095Coeff0 a f) (poleRhoNode095Coeff1 a f) (poleRhoNode095Coeff2 a f) (poleRhoNode095Coeff3 a f) (poleRhoNode095Coeff4 a f) (poleRhoNode063Coeff0 a f) (poleRhoNode063Coeff1 a f) (poleRhoNode063Coeff2 a f) (poleRhoNode063Coeff3 a f) (poleRhoNode063Coeff4 a f) (poleRhoNode063Coeff5 a f) (poleRhoNode063Coeff6 a f) (poleRhoNode063Coeff7 a f)

theorem poleRhoScalar16_eval (a f rho : ℝ) :
    poleRhoScalar16 a f rho=(poleRhoScalar16Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar16 poleRhoScalar16Coeff0
  ring

theorem poleRhoNode098_eval (a f rho : ℝ) :
    poleRhoNode098 a f rho=(((poleRhoNode098Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode098Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode098Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode098Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode098Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode098Coeff5 a f)*(rho)^(5 : ℕ)))) := by
  unfold poleRhoNode098
  rw [poleRhoScalar16_eval,poleRhoNode061_eval]
  simpa only [poleRhoNode098Coeff0,poleRhoNode098Coeff1,poleRhoNode098Coeff2,poleRhoNode098Coeff3,poleRhoNode098Coeff4,poleRhoNode098Coeff5] using
    pole_rho_mul_0_5 rho (poleRhoScalar16Coeff0 a f) (poleRhoNode061Coeff0 a f) (poleRhoNode061Coeff1 a f) (poleRhoNode061Coeff2 a f) (poleRhoNode061Coeff3 a f) (poleRhoNode061Coeff4 a f) (poleRhoNode061Coeff5 a f)

theorem poleRhoNode099_eval (a f rho : ℝ) :
    poleRhoNode099 a f rho=((((poleRhoNode099Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode099Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode099Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode099Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode099Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode099Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode099Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode099Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode099Coeff8 a f)*(rho)^(8 : ℕ)))+((poleRhoNode099Coeff9 a f)*(rho)^(9 : ℕ)+((poleRhoNode099Coeff10 a f)*(rho)^(10 : ℕ)+(poleRhoNode099Coeff11 a f)*(rho)^(11 : ℕ))))) := by
  unfold poleRhoNode099
  rw [poleRhoNode098_eval,poleRhoNode068_eval]
  simpa only [poleRhoNode099Coeff0,poleRhoNode099Coeff1,poleRhoNode099Coeff2,poleRhoNode099Coeff3,poleRhoNode099Coeff4,poleRhoNode099Coeff5,poleRhoNode099Coeff6,poleRhoNode099Coeff7,poleRhoNode099Coeff8,poleRhoNode099Coeff9,poleRhoNode099Coeff10,poleRhoNode099Coeff11] using
    pole_rho_mul_5_6 rho (poleRhoNode098Coeff0 a f) (poleRhoNode098Coeff1 a f) (poleRhoNode098Coeff2 a f) (poleRhoNode098Coeff3 a f) (poleRhoNode098Coeff4 a f) (poleRhoNode098Coeff5 a f) (poleRhoNode068Coeff0 a f) (poleRhoNode068Coeff1 a f) (poleRhoNode068Coeff2 a f) (poleRhoNode068Coeff3 a f) (poleRhoNode068Coeff4 a f) (poleRhoNode068Coeff5 a f) (poleRhoNode068Coeff6 a f)

theorem poleRhoNode100_eval (a f rho : ℝ) :
    poleRhoNode100 a f rho=((((poleRhoNode100Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode100Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode100Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode100Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode100Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode100Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode100Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode100Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode100Coeff8 a f)*(rho)^(8 : ℕ)))+((poleRhoNode100Coeff9 a f)*(rho)^(9 : ℕ)+((poleRhoNode100Coeff10 a f)*(rho)^(10 : ℕ)+(poleRhoNode100Coeff11 a f)*(rho)^(11 : ℕ))))) := by
  unfold poleRhoNode100
  rw [poleRhoNode087_eval,poleRhoNode090_eval]
  simpa only [poleRhoNode100Coeff0,poleRhoNode100Coeff1,poleRhoNode100Coeff2,poleRhoNode100Coeff3,poleRhoNode100Coeff4,poleRhoNode100Coeff5,poleRhoNode100Coeff6,poleRhoNode100Coeff7,poleRhoNode100Coeff8,poleRhoNode100Coeff9,poleRhoNode100Coeff10,poleRhoNode100Coeff11] using
    pole_rho_add_11_11 rho (poleRhoNode087Coeff0 a f) (poleRhoNode087Coeff1 a f) (poleRhoNode087Coeff2 a f) (poleRhoNode087Coeff3 a f) (poleRhoNode087Coeff4 a f) (poleRhoNode087Coeff5 a f) (poleRhoNode087Coeff6 a f) (poleRhoNode087Coeff7 a f) (poleRhoNode087Coeff8 a f) (poleRhoNode087Coeff9 a f) (poleRhoNode087Coeff10 a f) (poleRhoNode087Coeff11 a f) (poleRhoNode090Coeff0 a f) (poleRhoNode090Coeff1 a f) (poleRhoNode090Coeff2 a f) (poleRhoNode090Coeff3 a f) (poleRhoNode090Coeff4 a f) (poleRhoNode090Coeff5 a f) (poleRhoNode090Coeff6 a f) (poleRhoNode090Coeff7 a f) (poleRhoNode090Coeff8 a f) (poleRhoNode090Coeff9 a f) (poleRhoNode090Coeff10 a f) (poleRhoNode090Coeff11 a f)

theorem poleRhoNode101_eval (a f rho : ℝ) :
    poleRhoNode101 a f rho=((((poleRhoNode101Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode101Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode101Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode101Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode101Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode101Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode101Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode101Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode101Coeff8 a f)*(rho)^(8 : ℕ)))+((poleRhoNode101Coeff9 a f)*(rho)^(9 : ℕ)+((poleRhoNode101Coeff10 a f)*(rho)^(10 : ℕ)+(poleRhoNode101Coeff11 a f)*(rho)^(11 : ℕ))))) := by
  unfold poleRhoNode101
  rw [poleRhoNode084_eval,poleRhoNode100_eval]
  simpa only [poleRhoNode101Coeff0,poleRhoNode101Coeff1,poleRhoNode101Coeff2,poleRhoNode101Coeff3,poleRhoNode101Coeff4,poleRhoNode101Coeff5,poleRhoNode101Coeff6,poleRhoNode101Coeff7,poleRhoNode101Coeff8,poleRhoNode101Coeff9,poleRhoNode101Coeff10,poleRhoNode101Coeff11] using
    pole_rho_add_11_11 rho (poleRhoNode084Coeff0 a f) (poleRhoNode084Coeff1 a f) (poleRhoNode084Coeff2 a f) (poleRhoNode084Coeff3 a f) (poleRhoNode084Coeff4 a f) (poleRhoNode084Coeff5 a f) (poleRhoNode084Coeff6 a f) (poleRhoNode084Coeff7 a f) (poleRhoNode084Coeff8 a f) (poleRhoNode084Coeff9 a f) (poleRhoNode084Coeff10 a f) (poleRhoNode084Coeff11 a f) (poleRhoNode100Coeff0 a f) (poleRhoNode100Coeff1 a f) (poleRhoNode100Coeff2 a f) (poleRhoNode100Coeff3 a f) (poleRhoNode100Coeff4 a f) (poleRhoNode100Coeff5 a f) (poleRhoNode100Coeff6 a f) (poleRhoNode100Coeff7 a f) (poleRhoNode100Coeff8 a f) (poleRhoNode100Coeff9 a f) (poleRhoNode100Coeff10 a f) (poleRhoNode100Coeff11 a f)

theorem poleRhoNode102_eval (a f rho : ℝ) :
    poleRhoNode102 a f rho=((((poleRhoNode102Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode102Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode102Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode102Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode102Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode102Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode102Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode102Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode102Coeff8 a f)*(rho)^(8 : ℕ)))+((poleRhoNode102Coeff9 a f)*(rho)^(9 : ℕ)+((poleRhoNode102Coeff10 a f)*(rho)^(10 : ℕ)+(poleRhoNode102Coeff11 a f)*(rho)^(11 : ℕ))))) := by
  unfold poleRhoNode102
  rw [poleRhoNode096_eval,poleRhoNode099_eval]
  simpa only [poleRhoNode102Coeff0,poleRhoNode102Coeff1,poleRhoNode102Coeff2,poleRhoNode102Coeff3,poleRhoNode102Coeff4,poleRhoNode102Coeff5,poleRhoNode102Coeff6,poleRhoNode102Coeff7,poleRhoNode102Coeff8,poleRhoNode102Coeff9,poleRhoNode102Coeff10,poleRhoNode102Coeff11] using
    pole_rho_add_11_11 rho (poleRhoNode096Coeff0 a f) (poleRhoNode096Coeff1 a f) (poleRhoNode096Coeff2 a f) (poleRhoNode096Coeff3 a f) (poleRhoNode096Coeff4 a f) (poleRhoNode096Coeff5 a f) (poleRhoNode096Coeff6 a f) (poleRhoNode096Coeff7 a f) (poleRhoNode096Coeff8 a f) (poleRhoNode096Coeff9 a f) (poleRhoNode096Coeff10 a f) (poleRhoNode096Coeff11 a f) (poleRhoNode099Coeff0 a f) (poleRhoNode099Coeff1 a f) (poleRhoNode099Coeff2 a f) (poleRhoNode099Coeff3 a f) (poleRhoNode099Coeff4 a f) (poleRhoNode099Coeff5 a f) (poleRhoNode099Coeff6 a f) (poleRhoNode099Coeff7 a f) (poleRhoNode099Coeff8 a f) (poleRhoNode099Coeff9 a f) (poleRhoNode099Coeff10 a f) (poleRhoNode099Coeff11 a f)

theorem poleRhoNode103_eval (a f rho : ℝ) :
    poleRhoNode103 a f rho=((((poleRhoNode103Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode103Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode103Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode103Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode103Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode103Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode103Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode103Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode103Coeff8 a f)*(rho)^(8 : ℕ)))+((poleRhoNode103Coeff9 a f)*(rho)^(9 : ℕ)+((poleRhoNode103Coeff10 a f)*(rho)^(10 : ℕ)+(poleRhoNode103Coeff11 a f)*(rho)^(11 : ℕ))))) := by
  unfold poleRhoNode103
  rw [poleRhoNode093_eval,poleRhoNode102_eval]
  simpa only [poleRhoNode103Coeff0,poleRhoNode103Coeff1,poleRhoNode103Coeff2,poleRhoNode103Coeff3,poleRhoNode103Coeff4,poleRhoNode103Coeff5,poleRhoNode103Coeff6,poleRhoNode103Coeff7,poleRhoNode103Coeff8,poleRhoNode103Coeff9,poleRhoNode103Coeff10,poleRhoNode103Coeff11] using
    pole_rho_add_11_11 rho (poleRhoNode093Coeff0 a f) (poleRhoNode093Coeff1 a f) (poleRhoNode093Coeff2 a f) (poleRhoNode093Coeff3 a f) (poleRhoNode093Coeff4 a f) (poleRhoNode093Coeff5 a f) (poleRhoNode093Coeff6 a f) (poleRhoNode093Coeff7 a f) (poleRhoNode093Coeff8 a f) (poleRhoNode093Coeff9 a f) (poleRhoNode093Coeff10 a f) (poleRhoNode093Coeff11 a f) (poleRhoNode102Coeff0 a f) (poleRhoNode102Coeff1 a f) (poleRhoNode102Coeff2 a f) (poleRhoNode102Coeff3 a f) (poleRhoNode102Coeff4 a f) (poleRhoNode102Coeff5 a f) (poleRhoNode102Coeff6 a f) (poleRhoNode102Coeff7 a f) (poleRhoNode102Coeff8 a f) (poleRhoNode102Coeff9 a f) (poleRhoNode102Coeff10 a f) (poleRhoNode102Coeff11 a f)

theorem poleRhoNode104_eval (a f rho : ℝ) :
    poleRhoNode104 a f rho=((((poleRhoNode104Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode104Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode104Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode104Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode104Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode104Coeff5 a f)*(rho)^(5 : ℕ))))+(((poleRhoNode104Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode104Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode104Coeff8 a f)*(rho)^(8 : ℕ)))+((poleRhoNode104Coeff9 a f)*(rho)^(9 : ℕ)+((poleRhoNode104Coeff10 a f)*(rho)^(10 : ℕ)+(poleRhoNode104Coeff11 a f)*(rho)^(11 : ℕ))))) := by
  unfold poleRhoNode104
  rw [poleRhoNode101_eval,poleRhoNode103_eval]
  simpa only [poleRhoNode104Coeff0,poleRhoNode104Coeff1,poleRhoNode104Coeff2,poleRhoNode104Coeff3,poleRhoNode104Coeff4,poleRhoNode104Coeff5,poleRhoNode104Coeff6,poleRhoNode104Coeff7,poleRhoNode104Coeff8,poleRhoNode104Coeff9,poleRhoNode104Coeff10,poleRhoNode104Coeff11] using
    pole_rho_add_11_11 rho (poleRhoNode101Coeff0 a f) (poleRhoNode101Coeff1 a f) (poleRhoNode101Coeff2 a f) (poleRhoNode101Coeff3 a f) (poleRhoNode101Coeff4 a f) (poleRhoNode101Coeff5 a f) (poleRhoNode101Coeff6 a f) (poleRhoNode101Coeff7 a f) (poleRhoNode101Coeff8 a f) (poleRhoNode101Coeff9 a f) (poleRhoNode101Coeff10 a f) (poleRhoNode101Coeff11 a f) (poleRhoNode103Coeff0 a f) (poleRhoNode103Coeff1 a f) (poleRhoNode103Coeff2 a f) (poleRhoNode103Coeff3 a f) (poleRhoNode103Coeff4 a f) (poleRhoNode103Coeff5 a f) (poleRhoNode103Coeff6 a f) (poleRhoNode103Coeff7 a f) (poleRhoNode103Coeff8 a f) (poleRhoNode103Coeff9 a f) (poleRhoNode103Coeff10 a f) (poleRhoNode103Coeff11 a f)

theorem poleRhoInvariant2_eval (a f rho : ℝ) :
    poleRhoInvariant2 a f rho=(poleRhoInvariant2Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoInvariant2 poleRhoInvariant2Coeff0
  ring

theorem poleRhoNode106_eval (a f rho : ℝ) :
    poleRhoNode106 a f rho=(((poleRhoNode106Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode106Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode106Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode106Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode106
  rw [poleRhoInvariant2_eval,poleRhoNode022_eval]
  simpa only [poleRhoNode106Coeff0,poleRhoNode106Coeff1,poleRhoNode106Coeff2,poleRhoNode106Coeff3] using
    pole_rho_mul_0_3 rho (poleRhoInvariant2Coeff0 a f) (poleRhoNode022Coeff0 a f) (poleRhoNode022Coeff1 a f) (poleRhoNode022Coeff2 a f) (poleRhoNode022Coeff3 a f)

theorem poleRhoNode107_eval (a f rho : ℝ) :
    poleRhoNode107 a f rho=(((poleRhoNode107Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode107Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode107Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoNode107Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode107Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoNode107Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode107Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoNode107
  rw [poleRhoNode025_eval,poleRhoUpper2_eval]
  simpa only [poleRhoNode107Coeff0,poleRhoNode107Coeff1,poleRhoNode107Coeff2,poleRhoNode107Coeff3,poleRhoNode107Coeff4,poleRhoNode107Coeff5,poleRhoNode107Coeff6] using
    pole_rho_mul_2_4 rho (poleRhoNode025Coeff0 a f) (poleRhoNode025Coeff1 a f) (poleRhoNode025Coeff2 a f) (poleRhoUpper2Coeff0 a f) (poleRhoUpper2Coeff1 a f) (poleRhoUpper2Coeff2 a f) (poleRhoUpper2Coeff3 a f) (poleRhoUpper2Coeff4 a f)

theorem poleRhoNode108_eval (a f rho : ℝ) :
    poleRhoNode108 a f rho=((((poleRhoNode108Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode108Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode108Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode108Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode108Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode108Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode108Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode108Coeff7 a f)*(rho)^(7 : ℕ)))) := by
  unfold poleRhoNode108
  rw [poleRhoG_eval,poleRhoNode107_eval]
  simpa only [poleRhoNode108Coeff0,poleRhoNode108Coeff1,poleRhoNode108Coeff2,poleRhoNode108Coeff3,poleRhoNode108Coeff4,poleRhoNode108Coeff5,poleRhoNode108Coeff6,poleRhoNode108Coeff7] using
    pole_rho_mul_1_6 rho (poleRhoGCoeff0 a f) (poleRhoGCoeff1 a f) (poleRhoNode107Coeff0 a f) (poleRhoNode107Coeff1 a f) (poleRhoNode107Coeff2 a f) (poleRhoNode107Coeff3 a f) (poleRhoNode107Coeff4 a f) (poleRhoNode107Coeff5 a f) (poleRhoNode107Coeff6 a f)

theorem poleRhoNode109_eval (a f rho : ℝ) :
    poleRhoNode109 a f rho=((((poleRhoNode109Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode109Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode109Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode109Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode109Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode109Coeff5 a f)*(rho)^(5 : ℕ)+((poleRhoNode109Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode109Coeff7 a f)*(rho)^(7 : ℕ)))+((poleRhoNode109Coeff8 a f)*(rho)^(8 : ℕ)+((poleRhoNode109Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode109Coeff10 a f)*(rho)^(10 : ℕ))))) := by
  unfold poleRhoNode109
  rw [poleRhoNode106_eval,poleRhoNode108_eval]
  simpa only [poleRhoNode109Coeff0,poleRhoNode109Coeff1,poleRhoNode109Coeff2,poleRhoNode109Coeff3,poleRhoNode109Coeff4,poleRhoNode109Coeff5,poleRhoNode109Coeff6,poleRhoNode109Coeff7,poleRhoNode109Coeff8,poleRhoNode109Coeff9,poleRhoNode109Coeff10] using
    pole_rho_mul_3_7 rho (poleRhoNode106Coeff0 a f) (poleRhoNode106Coeff1 a f) (poleRhoNode106Coeff2 a f) (poleRhoNode106Coeff3 a f) (poleRhoNode108Coeff0 a f) (poleRhoNode108Coeff1 a f) (poleRhoNode108Coeff2 a f) (poleRhoNode108Coeff3 a f) (poleRhoNode108Coeff4 a f) (poleRhoNode108Coeff5 a f) (poleRhoNode108Coeff6 a f) (poleRhoNode108Coeff7 a f)

theorem poleRhoScalar22_eval (a f rho : ℝ) :
    poleRhoScalar22 a f rho=(poleRhoScalar22Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar22 poleRhoScalar22Coeff0
  ring

theorem poleRhoNode111_eval (a f rho : ℝ) :
    poleRhoNode111 a f rho=(poleRhoNode111Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoNode111
  rw [poleRhoScalar22_eval,poleRhoOne_eval]
  simpa only [poleRhoNode111Coeff0] using
    pole_rho_mul_0_0 rho (poleRhoScalar22Coeff0 a f) (poleRhoOneCoeff0 a f)

theorem poleRhoNode112_eval (a f rho : ℝ) :
    poleRhoNode112 a f rho=((((poleRhoNode112Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode112Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode112Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode112Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode112Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode112Coeff5 a f)*(rho)^(5 : ℕ)+((poleRhoNode112Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode112Coeff7 a f)*(rho)^(7 : ℕ)))+((poleRhoNode112Coeff8 a f)*(rho)^(8 : ℕ)+((poleRhoNode112Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode112Coeff10 a f)*(rho)^(10 : ℕ))))) := by
  unfold poleRhoNode112
  rw [poleRhoNode111_eval,poleRhoNode048_eval]
  simpa only [poleRhoNode112Coeff0,poleRhoNode112Coeff1,poleRhoNode112Coeff2,poleRhoNode112Coeff3,poleRhoNode112Coeff4,poleRhoNode112Coeff5,poleRhoNode112Coeff6,poleRhoNode112Coeff7,poleRhoNode112Coeff8,poleRhoNode112Coeff9,poleRhoNode112Coeff10] using
    pole_rho_mul_0_10 rho (poleRhoNode111Coeff0 a f) (poleRhoNode048Coeff0 a f) (poleRhoNode048Coeff1 a f) (poleRhoNode048Coeff2 a f) (poleRhoNode048Coeff3 a f) (poleRhoNode048Coeff4 a f) (poleRhoNode048Coeff5 a f) (poleRhoNode048Coeff6 a f) (poleRhoNode048Coeff7 a f) (poleRhoNode048Coeff8 a f) (poleRhoNode048Coeff9 a f) (poleRhoNode048Coeff10 a f)

theorem poleRhoScalar23_eval (a f rho : ℝ) :
    poleRhoScalar23 a f rho=(poleRhoScalar23Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar23 poleRhoScalar23Coeff0
  ring

theorem poleRhoNode114_eval (a f rho : ℝ) :
    poleRhoNode114 a f rho=((poleRhoNode114Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode114Coeff1 a f)*(rho)^(1 : ℕ)) := by
  unfold poleRhoNode114
  rw [poleRhoScalar23_eval,poleRhoBase_eval]
  simpa only [poleRhoNode114Coeff0,poleRhoNode114Coeff1] using
    pole_rho_mul_0_1 rho (poleRhoScalar23Coeff0 a f) (poleRhoBaseCoeff0 a f) (poleRhoBaseCoeff1 a f)

theorem poleRhoNode115_eval (a f rho : ℝ) :
    poleRhoNode115 a f rho=((((poleRhoNode115Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode115Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode115Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode115Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode115Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode115Coeff5 a f)*(rho)^(5 : ℕ)+((poleRhoNode115Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode115Coeff7 a f)*(rho)^(7 : ℕ)))+((poleRhoNode115Coeff8 a f)*(rho)^(8 : ℕ)+((poleRhoNode115Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode115Coeff10 a f)*(rho)^(10 : ℕ))))) := by
  unfold poleRhoNode115
  rw [poleRhoNode114_eval,poleRhoNode053_eval]
  simpa only [poleRhoNode115Coeff0,poleRhoNode115Coeff1,poleRhoNode115Coeff2,poleRhoNode115Coeff3,poleRhoNode115Coeff4,poleRhoNode115Coeff5,poleRhoNode115Coeff6,poleRhoNode115Coeff7,poleRhoNode115Coeff8,poleRhoNode115Coeff9,poleRhoNode115Coeff10] using
    pole_rho_mul_1_9 rho (poleRhoNode114Coeff0 a f) (poleRhoNode114Coeff1 a f) (poleRhoNode053Coeff0 a f) (poleRhoNode053Coeff1 a f) (poleRhoNode053Coeff2 a f) (poleRhoNode053Coeff3 a f) (poleRhoNode053Coeff4 a f) (poleRhoNode053Coeff5 a f) (poleRhoNode053Coeff6 a f) (poleRhoNode053Coeff7 a f) (poleRhoNode053Coeff8 a f) (poleRhoNode053Coeff9 a f)

theorem poleRhoScalar24_eval (a f rho : ℝ) :
    poleRhoScalar24 a f rho=(poleRhoScalar24Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar24 poleRhoScalar24Coeff0
  ring

theorem poleRhoNode117_eval (a f rho : ℝ) :
    poleRhoNode117 a f rho=((poleRhoNode117Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode117Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode117Coeff2 a f)*(rho)^(2 : ℕ))) := by
  unfold poleRhoNode117
  rw [poleRhoScalar24_eval,poleRhoNode046_eval]
  simpa only [poleRhoNode117Coeff0,poleRhoNode117Coeff1,poleRhoNode117Coeff2] using
    pole_rho_mul_0_2 rho (poleRhoScalar24Coeff0 a f) (poleRhoNode046Coeff0 a f) (poleRhoNode046Coeff1 a f) (poleRhoNode046Coeff2 a f)

theorem poleRhoNode118_eval (a f rho : ℝ) :
    poleRhoNode118 a f rho=((((poleRhoNode118Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode118Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode118Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode118Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode118Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode118Coeff5 a f)*(rho)^(5 : ℕ)+((poleRhoNode118Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode118Coeff7 a f)*(rho)^(7 : ℕ)))+((poleRhoNode118Coeff8 a f)*(rho)^(8 : ℕ)+((poleRhoNode118Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode118Coeff10 a f)*(rho)^(10 : ℕ))))) := by
  unfold poleRhoNode118
  rw [poleRhoNode117_eval,poleRhoNode058_eval]
  simpa only [poleRhoNode118Coeff0,poleRhoNode118Coeff1,poleRhoNode118Coeff2,poleRhoNode118Coeff3,poleRhoNode118Coeff4,poleRhoNode118Coeff5,poleRhoNode118Coeff6,poleRhoNode118Coeff7,poleRhoNode118Coeff8,poleRhoNode118Coeff9,poleRhoNode118Coeff10] using
    pole_rho_mul_2_8 rho (poleRhoNode117Coeff0 a f) (poleRhoNode117Coeff1 a f) (poleRhoNode117Coeff2 a f) (poleRhoNode058Coeff0 a f) (poleRhoNode058Coeff1 a f) (poleRhoNode058Coeff2 a f) (poleRhoNode058Coeff3 a f) (poleRhoNode058Coeff4 a f) (poleRhoNode058Coeff5 a f) (poleRhoNode058Coeff6 a f) (poleRhoNode058Coeff7 a f) (poleRhoNode058Coeff8 a f)

theorem poleRhoScalar25_eval (a f rho : ℝ) :
    poleRhoScalar25 a f rho=(poleRhoScalar25Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar25 poleRhoScalar25Coeff0
  ring

theorem poleRhoNode120_eval (a f rho : ℝ) :
    poleRhoNode120 a f rho=(((poleRhoNode120Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode120Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode120Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode120Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode120
  rw [poleRhoScalar25_eval,poleRhoNode051_eval]
  simpa only [poleRhoNode120Coeff0,poleRhoNode120Coeff1,poleRhoNode120Coeff2,poleRhoNode120Coeff3] using
    pole_rho_mul_0_3 rho (poleRhoScalar25Coeff0 a f) (poleRhoNode051Coeff0 a f) (poleRhoNode051Coeff1 a f) (poleRhoNode051Coeff2 a f) (poleRhoNode051Coeff3 a f)

theorem poleRhoNode121_eval (a f rho : ℝ) :
    poleRhoNode121 a f rho=((((poleRhoNode121Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode121Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode121Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode121Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode121Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode121Coeff5 a f)*(rho)^(5 : ℕ)+((poleRhoNode121Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode121Coeff7 a f)*(rho)^(7 : ℕ)))+((poleRhoNode121Coeff8 a f)*(rho)^(8 : ℕ)+((poleRhoNode121Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode121Coeff10 a f)*(rho)^(10 : ℕ))))) := by
  unfold poleRhoNode121
  rw [poleRhoNode120_eval,poleRhoNode063_eval]
  simpa only [poleRhoNode121Coeff0,poleRhoNode121Coeff1,poleRhoNode121Coeff2,poleRhoNode121Coeff3,poleRhoNode121Coeff4,poleRhoNode121Coeff5,poleRhoNode121Coeff6,poleRhoNode121Coeff7,poleRhoNode121Coeff8,poleRhoNode121Coeff9,poleRhoNode121Coeff10] using
    pole_rho_mul_3_7 rho (poleRhoNode120Coeff0 a f) (poleRhoNode120Coeff1 a f) (poleRhoNode120Coeff2 a f) (poleRhoNode120Coeff3 a f) (poleRhoNode063Coeff0 a f) (poleRhoNode063Coeff1 a f) (poleRhoNode063Coeff2 a f) (poleRhoNode063Coeff3 a f) (poleRhoNode063Coeff4 a f) (poleRhoNode063Coeff5 a f) (poleRhoNode063Coeff6 a f) (poleRhoNode063Coeff7 a f)

theorem poleRhoScalar26_eval (a f rho : ℝ) :
    poleRhoScalar26 a f rho=(poleRhoScalar26Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar26 poleRhoScalar26Coeff0
  ring

theorem poleRhoNode123_eval (a f rho : ℝ) :
    poleRhoNode123 a f rho=(((poleRhoNode123Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode123Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode123Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode123Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode123Coeff4 a f)*(rho)^(4 : ℕ)))) := by
  unfold poleRhoNode123
  rw [poleRhoScalar26_eval,poleRhoNode056_eval]
  simpa only [poleRhoNode123Coeff0,poleRhoNode123Coeff1,poleRhoNode123Coeff2,poleRhoNode123Coeff3,poleRhoNode123Coeff4] using
    pole_rho_mul_0_4 rho (poleRhoScalar26Coeff0 a f) (poleRhoNode056Coeff0 a f) (poleRhoNode056Coeff1 a f) (poleRhoNode056Coeff2 a f) (poleRhoNode056Coeff3 a f) (poleRhoNode056Coeff4 a f)

theorem poleRhoNode124_eval (a f rho : ℝ) :
    poleRhoNode124 a f rho=((((poleRhoNode124Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode124Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode124Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode124Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode124Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode124Coeff5 a f)*(rho)^(5 : ℕ)+((poleRhoNode124Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode124Coeff7 a f)*(rho)^(7 : ℕ)))+((poleRhoNode124Coeff8 a f)*(rho)^(8 : ℕ)+((poleRhoNode124Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode124Coeff10 a f)*(rho)^(10 : ℕ))))) := by
  unfold poleRhoNode124
  rw [poleRhoNode123_eval,poleRhoNode068_eval]
  simpa only [poleRhoNode124Coeff0,poleRhoNode124Coeff1,poleRhoNode124Coeff2,poleRhoNode124Coeff3,poleRhoNode124Coeff4,poleRhoNode124Coeff5,poleRhoNode124Coeff6,poleRhoNode124Coeff7,poleRhoNode124Coeff8,poleRhoNode124Coeff9,poleRhoNode124Coeff10] using
    pole_rho_mul_4_6 rho (poleRhoNode123Coeff0 a f) (poleRhoNode123Coeff1 a f) (poleRhoNode123Coeff2 a f) (poleRhoNode123Coeff3 a f) (poleRhoNode123Coeff4 a f) (poleRhoNode068Coeff0 a f) (poleRhoNode068Coeff1 a f) (poleRhoNode068Coeff2 a f) (poleRhoNode068Coeff3 a f) (poleRhoNode068Coeff4 a f) (poleRhoNode068Coeff5 a f) (poleRhoNode068Coeff6 a f)

theorem poleRhoNode125_eval (a f rho : ℝ) :
    poleRhoNode125 a f rho=((((poleRhoNode125Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode125Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode125Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode125Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode125Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode125Coeff5 a f)*(rho)^(5 : ℕ)+((poleRhoNode125Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode125Coeff7 a f)*(rho)^(7 : ℕ)))+((poleRhoNode125Coeff8 a f)*(rho)^(8 : ℕ)+((poleRhoNode125Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode125Coeff10 a f)*(rho)^(10 : ℕ))))) := by
  unfold poleRhoNode125
  rw [poleRhoNode112_eval,poleRhoNode115_eval]
  simpa only [poleRhoNode125Coeff0,poleRhoNode125Coeff1,poleRhoNode125Coeff2,poleRhoNode125Coeff3,poleRhoNode125Coeff4,poleRhoNode125Coeff5,poleRhoNode125Coeff6,poleRhoNode125Coeff7,poleRhoNode125Coeff8,poleRhoNode125Coeff9,poleRhoNode125Coeff10] using
    pole_rho_add_10_10 rho (poleRhoNode112Coeff0 a f) (poleRhoNode112Coeff1 a f) (poleRhoNode112Coeff2 a f) (poleRhoNode112Coeff3 a f) (poleRhoNode112Coeff4 a f) (poleRhoNode112Coeff5 a f) (poleRhoNode112Coeff6 a f) (poleRhoNode112Coeff7 a f) (poleRhoNode112Coeff8 a f) (poleRhoNode112Coeff9 a f) (poleRhoNode112Coeff10 a f) (poleRhoNode115Coeff0 a f) (poleRhoNode115Coeff1 a f) (poleRhoNode115Coeff2 a f) (poleRhoNode115Coeff3 a f) (poleRhoNode115Coeff4 a f) (poleRhoNode115Coeff5 a f) (poleRhoNode115Coeff6 a f) (poleRhoNode115Coeff7 a f) (poleRhoNode115Coeff8 a f) (poleRhoNode115Coeff9 a f) (poleRhoNode115Coeff10 a f)

theorem poleRhoNode126_eval (a f rho : ℝ) :
    poleRhoNode126 a f rho=((((poleRhoNode126Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode126Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode126Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode126Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode126Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode126Coeff5 a f)*(rho)^(5 : ℕ)+((poleRhoNode126Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode126Coeff7 a f)*(rho)^(7 : ℕ)))+((poleRhoNode126Coeff8 a f)*(rho)^(8 : ℕ)+((poleRhoNode126Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode126Coeff10 a f)*(rho)^(10 : ℕ))))) := by
  unfold poleRhoNode126
  rw [poleRhoNode121_eval,poleRhoNode124_eval]
  simpa only [poleRhoNode126Coeff0,poleRhoNode126Coeff1,poleRhoNode126Coeff2,poleRhoNode126Coeff3,poleRhoNode126Coeff4,poleRhoNode126Coeff5,poleRhoNode126Coeff6,poleRhoNode126Coeff7,poleRhoNode126Coeff8,poleRhoNode126Coeff9,poleRhoNode126Coeff10] using
    pole_rho_add_10_10 rho (poleRhoNode121Coeff0 a f) (poleRhoNode121Coeff1 a f) (poleRhoNode121Coeff2 a f) (poleRhoNode121Coeff3 a f) (poleRhoNode121Coeff4 a f) (poleRhoNode121Coeff5 a f) (poleRhoNode121Coeff6 a f) (poleRhoNode121Coeff7 a f) (poleRhoNode121Coeff8 a f) (poleRhoNode121Coeff9 a f) (poleRhoNode121Coeff10 a f) (poleRhoNode124Coeff0 a f) (poleRhoNode124Coeff1 a f) (poleRhoNode124Coeff2 a f) (poleRhoNode124Coeff3 a f) (poleRhoNode124Coeff4 a f) (poleRhoNode124Coeff5 a f) (poleRhoNode124Coeff6 a f) (poleRhoNode124Coeff7 a f) (poleRhoNode124Coeff8 a f) (poleRhoNode124Coeff9 a f) (poleRhoNode124Coeff10 a f)

theorem poleRhoNode127_eval (a f rho : ℝ) :
    poleRhoNode127 a f rho=((((poleRhoNode127Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode127Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode127Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode127Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode127Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode127Coeff5 a f)*(rho)^(5 : ℕ)+((poleRhoNode127Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode127Coeff7 a f)*(rho)^(7 : ℕ)))+((poleRhoNode127Coeff8 a f)*(rho)^(8 : ℕ)+((poleRhoNode127Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode127Coeff10 a f)*(rho)^(10 : ℕ))))) := by
  unfold poleRhoNode127
  rw [poleRhoNode118_eval,poleRhoNode126_eval]
  simpa only [poleRhoNode127Coeff0,poleRhoNode127Coeff1,poleRhoNode127Coeff2,poleRhoNode127Coeff3,poleRhoNode127Coeff4,poleRhoNode127Coeff5,poleRhoNode127Coeff6,poleRhoNode127Coeff7,poleRhoNode127Coeff8,poleRhoNode127Coeff9,poleRhoNode127Coeff10] using
    pole_rho_add_10_10 rho (poleRhoNode118Coeff0 a f) (poleRhoNode118Coeff1 a f) (poleRhoNode118Coeff2 a f) (poleRhoNode118Coeff3 a f) (poleRhoNode118Coeff4 a f) (poleRhoNode118Coeff5 a f) (poleRhoNode118Coeff6 a f) (poleRhoNode118Coeff7 a f) (poleRhoNode118Coeff8 a f) (poleRhoNode118Coeff9 a f) (poleRhoNode118Coeff10 a f) (poleRhoNode126Coeff0 a f) (poleRhoNode126Coeff1 a f) (poleRhoNode126Coeff2 a f) (poleRhoNode126Coeff3 a f) (poleRhoNode126Coeff4 a f) (poleRhoNode126Coeff5 a f) (poleRhoNode126Coeff6 a f) (poleRhoNode126Coeff7 a f) (poleRhoNode126Coeff8 a f) (poleRhoNode126Coeff9 a f) (poleRhoNode126Coeff10 a f)

theorem poleRhoNode128_eval (a f rho : ℝ) :
    poleRhoNode128 a f rho=((((poleRhoNode128Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode128Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode128Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode128Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode128Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode128Coeff5 a f)*(rho)^(5 : ℕ)+((poleRhoNode128Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode128Coeff7 a f)*(rho)^(7 : ℕ)))+((poleRhoNode128Coeff8 a f)*(rho)^(8 : ℕ)+((poleRhoNode128Coeff9 a f)*(rho)^(9 : ℕ)+(poleRhoNode128Coeff10 a f)*(rho)^(10 : ℕ))))) := by
  unfold poleRhoNode128
  rw [poleRhoNode125_eval,poleRhoNode127_eval]
  simpa only [poleRhoNode128Coeff0,poleRhoNode128Coeff1,poleRhoNode128Coeff2,poleRhoNode128Coeff3,poleRhoNode128Coeff4,poleRhoNode128Coeff5,poleRhoNode128Coeff6,poleRhoNode128Coeff7,poleRhoNode128Coeff8,poleRhoNode128Coeff9,poleRhoNode128Coeff10] using
    pole_rho_add_10_10 rho (poleRhoNode125Coeff0 a f) (poleRhoNode125Coeff1 a f) (poleRhoNode125Coeff2 a f) (poleRhoNode125Coeff3 a f) (poleRhoNode125Coeff4 a f) (poleRhoNode125Coeff5 a f) (poleRhoNode125Coeff6 a f) (poleRhoNode125Coeff7 a f) (poleRhoNode125Coeff8 a f) (poleRhoNode125Coeff9 a f) (poleRhoNode125Coeff10 a f) (poleRhoNode127Coeff0 a f) (poleRhoNode127Coeff1 a f) (poleRhoNode127Coeff2 a f) (poleRhoNode127Coeff3 a f) (poleRhoNode127Coeff4 a f) (poleRhoNode127Coeff5 a f) (poleRhoNode127Coeff6 a f) (poleRhoNode127Coeff7 a f) (poleRhoNode127Coeff8 a f) (poleRhoNode127Coeff9 a f) (poleRhoNode127Coeff10 a f)

theorem poleRhoInvariant3_eval (a f rho : ℝ) :
    poleRhoInvariant3 a f rho=(poleRhoInvariant3Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoInvariant3 poleRhoInvariant3Coeff0
  ring

theorem poleRhoNode130_eval (a f rho : ℝ) :
    poleRhoNode130 a f rho=(((poleRhoNode130Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode130Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode130Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode130Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode130
  rw [poleRhoInvariant3_eval,poleRhoNode022_eval]
  simpa only [poleRhoNode130Coeff0,poleRhoNode130Coeff1,poleRhoNode130Coeff2,poleRhoNode130Coeff3] using
    pole_rho_mul_0_3 rho (poleRhoInvariant3Coeff0 a f) (poleRhoNode022Coeff0 a f) (poleRhoNode022Coeff1 a f) (poleRhoNode022Coeff2 a f) (poleRhoNode022Coeff3 a f)

theorem poleRhoNode131_eval (a f rho : ℝ) :
    poleRhoNode131 a f rho=(((poleRhoNode131Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode131Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode131Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode131Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode131Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode131Coeff5 a f)*(rho)^(5 : ℕ)))) := by
  unfold poleRhoNode131
  rw [poleRhoS_eval,poleRhoUpper3_eval]
  simpa only [poleRhoNode131Coeff0,poleRhoNode131Coeff1,poleRhoNode131Coeff2,poleRhoNode131Coeff3,poleRhoNode131Coeff4,poleRhoNode131Coeff5] using
    pole_rho_mul_1_4 rho (poleRhoSCoeff0 a f) (poleRhoSCoeff1 a f) (poleRhoUpper3Coeff0 a f) (poleRhoUpper3Coeff1 a f) (poleRhoUpper3Coeff2 a f) (poleRhoUpper3Coeff3 a f) (poleRhoUpper3Coeff4 a f)

theorem poleRhoNode132_eval (a f rho : ℝ) :
    poleRhoNode132 a f rho=(((poleRhoNode132Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode132Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode132Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoNode132Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode132Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoNode132Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode132Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoNode132
  rw [poleRhoG_eval,poleRhoNode131_eval]
  simpa only [poleRhoNode132Coeff0,poleRhoNode132Coeff1,poleRhoNode132Coeff2,poleRhoNode132Coeff3,poleRhoNode132Coeff4,poleRhoNode132Coeff5,poleRhoNode132Coeff6] using
    pole_rho_mul_1_5 rho (poleRhoGCoeff0 a f) (poleRhoGCoeff1 a f) (poleRhoNode131Coeff0 a f) (poleRhoNode131Coeff1 a f) (poleRhoNode131Coeff2 a f) (poleRhoNode131Coeff3 a f) (poleRhoNode131Coeff4 a f) (poleRhoNode131Coeff5 a f)

theorem poleRhoNode133_eval (a f rho : ℝ) :
    poleRhoNode133 a f rho=((((poleRhoNode133Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode133Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode133Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode133Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode133Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode133Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode133Coeff6 a f)*(rho)^(6 : ℕ))+((poleRhoNode133Coeff7 a f)*(rho)^(7 : ℕ)+((poleRhoNode133Coeff8 a f)*(rho)^(8 : ℕ)+(poleRhoNode133Coeff9 a f)*(rho)^(9 : ℕ))))) := by
  unfold poleRhoNode133
  rw [poleRhoNode130_eval,poleRhoNode132_eval]
  simpa only [poleRhoNode133Coeff0,poleRhoNode133Coeff1,poleRhoNode133Coeff2,poleRhoNode133Coeff3,poleRhoNode133Coeff4,poleRhoNode133Coeff5,poleRhoNode133Coeff6,poleRhoNode133Coeff7,poleRhoNode133Coeff8,poleRhoNode133Coeff9] using
    pole_rho_mul_3_6 rho (poleRhoNode130Coeff0 a f) (poleRhoNode130Coeff1 a f) (poleRhoNode130Coeff2 a f) (poleRhoNode130Coeff3 a f) (poleRhoNode132Coeff0 a f) (poleRhoNode132Coeff1 a f) (poleRhoNode132Coeff2 a f) (poleRhoNode132Coeff3 a f) (poleRhoNode132Coeff4 a f) (poleRhoNode132Coeff5 a f) (poleRhoNode132Coeff6 a f)

theorem poleRhoScalar33_eval (a f rho : ℝ) :
    poleRhoScalar33 a f rho=(poleRhoScalar33Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar33 poleRhoScalar33Coeff0
  ring

theorem poleRhoNode135_eval (a f rho : ℝ) :
    poleRhoNode135 a f rho=(poleRhoNode135Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoNode135
  rw [poleRhoScalar33_eval,poleRhoOne_eval]
  simpa only [poleRhoNode135Coeff0] using
    pole_rho_mul_0_0 rho (poleRhoScalar33Coeff0 a f) (poleRhoOneCoeff0 a f)

theorem poleRhoNode136_eval (a f rho : ℝ) :
    poleRhoNode136 a f rho=((((poleRhoNode136Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode136Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode136Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode136Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode136Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode136Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode136Coeff6 a f)*(rho)^(6 : ℕ))+((poleRhoNode136Coeff7 a f)*(rho)^(7 : ℕ)+((poleRhoNode136Coeff8 a f)*(rho)^(8 : ℕ)+(poleRhoNode136Coeff9 a f)*(rho)^(9 : ℕ))))) := by
  unfold poleRhoNode136
  rw [poleRhoNode135_eval,poleRhoNode053_eval]
  simpa only [poleRhoNode136Coeff0,poleRhoNode136Coeff1,poleRhoNode136Coeff2,poleRhoNode136Coeff3,poleRhoNode136Coeff4,poleRhoNode136Coeff5,poleRhoNode136Coeff6,poleRhoNode136Coeff7,poleRhoNode136Coeff8,poleRhoNode136Coeff9] using
    pole_rho_mul_0_9 rho (poleRhoNode135Coeff0 a f) (poleRhoNode053Coeff0 a f) (poleRhoNode053Coeff1 a f) (poleRhoNode053Coeff2 a f) (poleRhoNode053Coeff3 a f) (poleRhoNode053Coeff4 a f) (poleRhoNode053Coeff5 a f) (poleRhoNode053Coeff6 a f) (poleRhoNode053Coeff7 a f) (poleRhoNode053Coeff8 a f) (poleRhoNode053Coeff9 a f)

theorem poleRhoScalar34_eval (a f rho : ℝ) :
    poleRhoScalar34 a f rho=(poleRhoScalar34Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar34 poleRhoScalar34Coeff0
  ring

theorem poleRhoNode138_eval (a f rho : ℝ) :
    poleRhoNode138 a f rho=((poleRhoNode138Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode138Coeff1 a f)*(rho)^(1 : ℕ)) := by
  unfold poleRhoNode138
  rw [poleRhoScalar34_eval,poleRhoBase_eval]
  simpa only [poleRhoNode138Coeff0,poleRhoNode138Coeff1] using
    pole_rho_mul_0_1 rho (poleRhoScalar34Coeff0 a f) (poleRhoBaseCoeff0 a f) (poleRhoBaseCoeff1 a f)

theorem poleRhoNode139_eval (a f rho : ℝ) :
    poleRhoNode139 a f rho=((((poleRhoNode139Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode139Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode139Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode139Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode139Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode139Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode139Coeff6 a f)*(rho)^(6 : ℕ))+((poleRhoNode139Coeff7 a f)*(rho)^(7 : ℕ)+((poleRhoNode139Coeff8 a f)*(rho)^(8 : ℕ)+(poleRhoNode139Coeff9 a f)*(rho)^(9 : ℕ))))) := by
  unfold poleRhoNode139
  rw [poleRhoNode138_eval,poleRhoNode058_eval]
  simpa only [poleRhoNode139Coeff0,poleRhoNode139Coeff1,poleRhoNode139Coeff2,poleRhoNode139Coeff3,poleRhoNode139Coeff4,poleRhoNode139Coeff5,poleRhoNode139Coeff6,poleRhoNode139Coeff7,poleRhoNode139Coeff8,poleRhoNode139Coeff9] using
    pole_rho_mul_1_8 rho (poleRhoNode138Coeff0 a f) (poleRhoNode138Coeff1 a f) (poleRhoNode058Coeff0 a f) (poleRhoNode058Coeff1 a f) (poleRhoNode058Coeff2 a f) (poleRhoNode058Coeff3 a f) (poleRhoNode058Coeff4 a f) (poleRhoNode058Coeff5 a f) (poleRhoNode058Coeff6 a f) (poleRhoNode058Coeff7 a f) (poleRhoNode058Coeff8 a f)

theorem poleRhoScalar35_eval (a f rho : ℝ) :
    poleRhoScalar35 a f rho=(poleRhoScalar35Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar35 poleRhoScalar35Coeff0
  ring

theorem poleRhoNode141_eval (a f rho : ℝ) :
    poleRhoNode141 a f rho=((poleRhoNode141Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode141Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode141Coeff2 a f)*(rho)^(2 : ℕ))) := by
  unfold poleRhoNode141
  rw [poleRhoScalar35_eval,poleRhoNode046_eval]
  simpa only [poleRhoNode141Coeff0,poleRhoNode141Coeff1,poleRhoNode141Coeff2] using
    pole_rho_mul_0_2 rho (poleRhoScalar35Coeff0 a f) (poleRhoNode046Coeff0 a f) (poleRhoNode046Coeff1 a f) (poleRhoNode046Coeff2 a f)

theorem poleRhoNode142_eval (a f rho : ℝ) :
    poleRhoNode142 a f rho=((((poleRhoNode142Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode142Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode142Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode142Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode142Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode142Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode142Coeff6 a f)*(rho)^(6 : ℕ))+((poleRhoNode142Coeff7 a f)*(rho)^(7 : ℕ)+((poleRhoNode142Coeff8 a f)*(rho)^(8 : ℕ)+(poleRhoNode142Coeff9 a f)*(rho)^(9 : ℕ))))) := by
  unfold poleRhoNode142
  rw [poleRhoNode141_eval,poleRhoNode063_eval]
  simpa only [poleRhoNode142Coeff0,poleRhoNode142Coeff1,poleRhoNode142Coeff2,poleRhoNode142Coeff3,poleRhoNode142Coeff4,poleRhoNode142Coeff5,poleRhoNode142Coeff6,poleRhoNode142Coeff7,poleRhoNode142Coeff8,poleRhoNode142Coeff9] using
    pole_rho_mul_2_7 rho (poleRhoNode141Coeff0 a f) (poleRhoNode141Coeff1 a f) (poleRhoNode141Coeff2 a f) (poleRhoNode063Coeff0 a f) (poleRhoNode063Coeff1 a f) (poleRhoNode063Coeff2 a f) (poleRhoNode063Coeff3 a f) (poleRhoNode063Coeff4 a f) (poleRhoNode063Coeff5 a f) (poleRhoNode063Coeff6 a f) (poleRhoNode063Coeff7 a f)

theorem poleRhoScalar36_eval (a f rho : ℝ) :
    poleRhoScalar36 a f rho=(poleRhoScalar36Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar36 poleRhoScalar36Coeff0
  ring

theorem poleRhoNode144_eval (a f rho : ℝ) :
    poleRhoNode144 a f rho=(((poleRhoNode144Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode144Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode144Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode144Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode144
  rw [poleRhoScalar36_eval,poleRhoNode051_eval]
  simpa only [poleRhoNode144Coeff0,poleRhoNode144Coeff1,poleRhoNode144Coeff2,poleRhoNode144Coeff3] using
    pole_rho_mul_0_3 rho (poleRhoScalar36Coeff0 a f) (poleRhoNode051Coeff0 a f) (poleRhoNode051Coeff1 a f) (poleRhoNode051Coeff2 a f) (poleRhoNode051Coeff3 a f)

theorem poleRhoNode145_eval (a f rho : ℝ) :
    poleRhoNode145 a f rho=((((poleRhoNode145Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode145Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode145Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode145Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode145Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode145Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode145Coeff6 a f)*(rho)^(6 : ℕ))+((poleRhoNode145Coeff7 a f)*(rho)^(7 : ℕ)+((poleRhoNode145Coeff8 a f)*(rho)^(8 : ℕ)+(poleRhoNode145Coeff9 a f)*(rho)^(9 : ℕ))))) := by
  unfold poleRhoNode145
  rw [poleRhoNode144_eval,poleRhoNode068_eval]
  simpa only [poleRhoNode145Coeff0,poleRhoNode145Coeff1,poleRhoNode145Coeff2,poleRhoNode145Coeff3,poleRhoNode145Coeff4,poleRhoNode145Coeff5,poleRhoNode145Coeff6,poleRhoNode145Coeff7,poleRhoNode145Coeff8,poleRhoNode145Coeff9] using
    pole_rho_mul_3_6 rho (poleRhoNode144Coeff0 a f) (poleRhoNode144Coeff1 a f) (poleRhoNode144Coeff2 a f) (poleRhoNode144Coeff3 a f) (poleRhoNode068Coeff0 a f) (poleRhoNode068Coeff1 a f) (poleRhoNode068Coeff2 a f) (poleRhoNode068Coeff3 a f) (poleRhoNode068Coeff4 a f) (poleRhoNode068Coeff5 a f) (poleRhoNode068Coeff6 a f)

theorem poleRhoNode146_eval (a f rho : ℝ) :
    poleRhoNode146 a f rho=((((poleRhoNode146Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode146Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode146Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode146Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode146Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode146Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode146Coeff6 a f)*(rho)^(6 : ℕ))+((poleRhoNode146Coeff7 a f)*(rho)^(7 : ℕ)+((poleRhoNode146Coeff8 a f)*(rho)^(8 : ℕ)+(poleRhoNode146Coeff9 a f)*(rho)^(9 : ℕ))))) := by
  unfold poleRhoNode146
  rw [poleRhoNode136_eval,poleRhoNode139_eval]
  simpa only [poleRhoNode146Coeff0,poleRhoNode146Coeff1,poleRhoNode146Coeff2,poleRhoNode146Coeff3,poleRhoNode146Coeff4,poleRhoNode146Coeff5,poleRhoNode146Coeff6,poleRhoNode146Coeff7,poleRhoNode146Coeff8,poleRhoNode146Coeff9] using
    pole_rho_add_9_9 rho (poleRhoNode136Coeff0 a f) (poleRhoNode136Coeff1 a f) (poleRhoNode136Coeff2 a f) (poleRhoNode136Coeff3 a f) (poleRhoNode136Coeff4 a f) (poleRhoNode136Coeff5 a f) (poleRhoNode136Coeff6 a f) (poleRhoNode136Coeff7 a f) (poleRhoNode136Coeff8 a f) (poleRhoNode136Coeff9 a f) (poleRhoNode139Coeff0 a f) (poleRhoNode139Coeff1 a f) (poleRhoNode139Coeff2 a f) (poleRhoNode139Coeff3 a f) (poleRhoNode139Coeff4 a f) (poleRhoNode139Coeff5 a f) (poleRhoNode139Coeff6 a f) (poleRhoNode139Coeff7 a f) (poleRhoNode139Coeff8 a f) (poleRhoNode139Coeff9 a f)

theorem poleRhoNode147_eval (a f rho : ℝ) :
    poleRhoNode147 a f rho=((((poleRhoNode147Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode147Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode147Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode147Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode147Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode147Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode147Coeff6 a f)*(rho)^(6 : ℕ))+((poleRhoNode147Coeff7 a f)*(rho)^(7 : ℕ)+((poleRhoNode147Coeff8 a f)*(rho)^(8 : ℕ)+(poleRhoNode147Coeff9 a f)*(rho)^(9 : ℕ))))) := by
  unfold poleRhoNode147
  rw [poleRhoNode142_eval,poleRhoNode145_eval]
  simpa only [poleRhoNode147Coeff0,poleRhoNode147Coeff1,poleRhoNode147Coeff2,poleRhoNode147Coeff3,poleRhoNode147Coeff4,poleRhoNode147Coeff5,poleRhoNode147Coeff6,poleRhoNode147Coeff7,poleRhoNode147Coeff8,poleRhoNode147Coeff9] using
    pole_rho_add_9_9 rho (poleRhoNode142Coeff0 a f) (poleRhoNode142Coeff1 a f) (poleRhoNode142Coeff2 a f) (poleRhoNode142Coeff3 a f) (poleRhoNode142Coeff4 a f) (poleRhoNode142Coeff5 a f) (poleRhoNode142Coeff6 a f) (poleRhoNode142Coeff7 a f) (poleRhoNode142Coeff8 a f) (poleRhoNode142Coeff9 a f) (poleRhoNode145Coeff0 a f) (poleRhoNode145Coeff1 a f) (poleRhoNode145Coeff2 a f) (poleRhoNode145Coeff3 a f) (poleRhoNode145Coeff4 a f) (poleRhoNode145Coeff5 a f) (poleRhoNode145Coeff6 a f) (poleRhoNode145Coeff7 a f) (poleRhoNode145Coeff8 a f) (poleRhoNode145Coeff9 a f)

theorem poleRhoNode148_eval (a f rho : ℝ) :
    poleRhoNode148 a f rho=((((poleRhoNode148Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode148Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode148Coeff2 a f)*(rho)^(2 : ℕ)+((poleRhoNode148Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode148Coeff4 a f)*(rho)^(4 : ℕ))))+(((poleRhoNode148Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode148Coeff6 a f)*(rho)^(6 : ℕ))+((poleRhoNode148Coeff7 a f)*(rho)^(7 : ℕ)+((poleRhoNode148Coeff8 a f)*(rho)^(8 : ℕ)+(poleRhoNode148Coeff9 a f)*(rho)^(9 : ℕ))))) := by
  unfold poleRhoNode148
  rw [poleRhoNode146_eval,poleRhoNode147_eval]
  simpa only [poleRhoNode148Coeff0,poleRhoNode148Coeff1,poleRhoNode148Coeff2,poleRhoNode148Coeff3,poleRhoNode148Coeff4,poleRhoNode148Coeff5,poleRhoNode148Coeff6,poleRhoNode148Coeff7,poleRhoNode148Coeff8,poleRhoNode148Coeff9] using
    pole_rho_add_9_9 rho (poleRhoNode146Coeff0 a f) (poleRhoNode146Coeff1 a f) (poleRhoNode146Coeff2 a f) (poleRhoNode146Coeff3 a f) (poleRhoNode146Coeff4 a f) (poleRhoNode146Coeff5 a f) (poleRhoNode146Coeff6 a f) (poleRhoNode146Coeff7 a f) (poleRhoNode146Coeff8 a f) (poleRhoNode146Coeff9 a f) (poleRhoNode147Coeff0 a f) (poleRhoNode147Coeff1 a f) (poleRhoNode147Coeff2 a f) (poleRhoNode147Coeff3 a f) (poleRhoNode147Coeff4 a f) (poleRhoNode147Coeff5 a f) (poleRhoNode147Coeff6 a f) (poleRhoNode147Coeff7 a f) (poleRhoNode147Coeff8 a f) (poleRhoNode147Coeff9 a f)

theorem poleRhoInvariant4_eval (a f rho : ℝ) :
    poleRhoInvariant4 a f rho=(poleRhoInvariant4Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoInvariant4 poleRhoInvariant4Coeff0
  ring

theorem poleRhoNode150_eval (a f rho : ℝ) :
    poleRhoNode150 a f rho=(((poleRhoNode150Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode150Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode150Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode150Coeff3 a f)*(rho)^(3 : ℕ))) := by
  unfold poleRhoNode150
  rw [poleRhoInvariant4_eval,poleRhoNode022_eval]
  simpa only [poleRhoNode150Coeff0,poleRhoNode150Coeff1,poleRhoNode150Coeff2,poleRhoNode150Coeff3] using
    pole_rho_mul_0_3 rho (poleRhoInvariant4Coeff0 a f) (poleRhoNode022Coeff0 a f) (poleRhoNode022Coeff1 a f) (poleRhoNode022Coeff2 a f) (poleRhoNode022Coeff3 a f)

theorem poleRhoNode151_eval (a f rho : ℝ) :
    poleRhoNode151 a f rho=(((poleRhoNode151Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode151Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode151Coeff2 a f)*(rho)^(2 : ℕ)))+((poleRhoNode151Coeff3 a f)*(rho)^(3 : ℕ)+((poleRhoNode151Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode151Coeff5 a f)*(rho)^(5 : ℕ)))) := by
  unfold poleRhoNode151
  rw [poleRhoG_eval,poleRhoUpper4_eval]
  simpa only [poleRhoNode151Coeff0,poleRhoNode151Coeff1,poleRhoNode151Coeff2,poleRhoNode151Coeff3,poleRhoNode151Coeff4,poleRhoNode151Coeff5] using
    pole_rho_mul_1_4 rho (poleRhoGCoeff0 a f) (poleRhoGCoeff1 a f) (poleRhoUpper4Coeff0 a f) (poleRhoUpper4Coeff1 a f) (poleRhoUpper4Coeff2 a f) (poleRhoUpper4Coeff3 a f) (poleRhoUpper4Coeff4 a f)

theorem poleRhoNode152_eval (a f rho : ℝ) :
    poleRhoNode152 a f rho=((((poleRhoNode152Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode152Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode152Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode152Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode152Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode152Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode152Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode152Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode152Coeff8 a f)*(rho)^(8 : ℕ))))) := by
  unfold poleRhoNode152
  rw [poleRhoNode150_eval,poleRhoNode151_eval]
  simpa only [poleRhoNode152Coeff0,poleRhoNode152Coeff1,poleRhoNode152Coeff2,poleRhoNode152Coeff3,poleRhoNode152Coeff4,poleRhoNode152Coeff5,poleRhoNode152Coeff6,poleRhoNode152Coeff7,poleRhoNode152Coeff8] using
    pole_rho_mul_3_5 rho (poleRhoNode150Coeff0 a f) (poleRhoNode150Coeff1 a f) (poleRhoNode150Coeff2 a f) (poleRhoNode150Coeff3 a f) (poleRhoNode151Coeff0 a f) (poleRhoNode151Coeff1 a f) (poleRhoNode151Coeff2 a f) (poleRhoNode151Coeff3 a f) (poleRhoNode151Coeff4 a f) (poleRhoNode151Coeff5 a f)

theorem poleRhoScalar44_eval (a f rho : ℝ) :
    poleRhoScalar44 a f rho=(poleRhoScalar44Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar44 poleRhoScalar44Coeff0
  ring

theorem poleRhoNode154_eval (a f rho : ℝ) :
    poleRhoNode154 a f rho=(poleRhoNode154Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoNode154
  rw [poleRhoScalar44_eval,poleRhoOne_eval]
  simpa only [poleRhoNode154Coeff0] using
    pole_rho_mul_0_0 rho (poleRhoScalar44Coeff0 a f) (poleRhoOneCoeff0 a f)

theorem poleRhoNode155_eval (a f rho : ℝ) :
    poleRhoNode155 a f rho=((((poleRhoNode155Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode155Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode155Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode155Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode155Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode155Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode155Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode155Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode155Coeff8 a f)*(rho)^(8 : ℕ))))) := by
  unfold poleRhoNode155
  rw [poleRhoNode154_eval,poleRhoNode058_eval]
  simpa only [poleRhoNode155Coeff0,poleRhoNode155Coeff1,poleRhoNode155Coeff2,poleRhoNode155Coeff3,poleRhoNode155Coeff4,poleRhoNode155Coeff5,poleRhoNode155Coeff6,poleRhoNode155Coeff7,poleRhoNode155Coeff8] using
    pole_rho_mul_0_8 rho (poleRhoNode154Coeff0 a f) (poleRhoNode058Coeff0 a f) (poleRhoNode058Coeff1 a f) (poleRhoNode058Coeff2 a f) (poleRhoNode058Coeff3 a f) (poleRhoNode058Coeff4 a f) (poleRhoNode058Coeff5 a f) (poleRhoNode058Coeff6 a f) (poleRhoNode058Coeff7 a f) (poleRhoNode058Coeff8 a f)

theorem poleRhoScalar45_eval (a f rho : ℝ) :
    poleRhoScalar45 a f rho=(poleRhoScalar45Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar45 poleRhoScalar45Coeff0
  ring

theorem poleRhoNode157_eval (a f rho : ℝ) :
    poleRhoNode157 a f rho=((poleRhoNode157Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode157Coeff1 a f)*(rho)^(1 : ℕ)) := by
  unfold poleRhoNode157
  rw [poleRhoScalar45_eval,poleRhoBase_eval]
  simpa only [poleRhoNode157Coeff0,poleRhoNode157Coeff1] using
    pole_rho_mul_0_1 rho (poleRhoScalar45Coeff0 a f) (poleRhoBaseCoeff0 a f) (poleRhoBaseCoeff1 a f)

theorem poleRhoNode158_eval (a f rho : ℝ) :
    poleRhoNode158 a f rho=((((poleRhoNode158Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode158Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode158Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode158Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode158Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode158Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode158Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode158Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode158Coeff8 a f)*(rho)^(8 : ℕ))))) := by
  unfold poleRhoNode158
  rw [poleRhoNode157_eval,poleRhoNode063_eval]
  simpa only [poleRhoNode158Coeff0,poleRhoNode158Coeff1,poleRhoNode158Coeff2,poleRhoNode158Coeff3,poleRhoNode158Coeff4,poleRhoNode158Coeff5,poleRhoNode158Coeff6,poleRhoNode158Coeff7,poleRhoNode158Coeff8] using
    pole_rho_mul_1_7 rho (poleRhoNode157Coeff0 a f) (poleRhoNode157Coeff1 a f) (poleRhoNode063Coeff0 a f) (poleRhoNode063Coeff1 a f) (poleRhoNode063Coeff2 a f) (poleRhoNode063Coeff3 a f) (poleRhoNode063Coeff4 a f) (poleRhoNode063Coeff5 a f) (poleRhoNode063Coeff6 a f) (poleRhoNode063Coeff7 a f)

theorem poleRhoScalar46_eval (a f rho : ℝ) :
    poleRhoScalar46 a f rho=(poleRhoScalar46Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar46 poleRhoScalar46Coeff0
  ring

theorem poleRhoNode160_eval (a f rho : ℝ) :
    poleRhoNode160 a f rho=((poleRhoNode160Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode160Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode160Coeff2 a f)*(rho)^(2 : ℕ))) := by
  unfold poleRhoNode160
  rw [poleRhoScalar46_eval,poleRhoNode046_eval]
  simpa only [poleRhoNode160Coeff0,poleRhoNode160Coeff1,poleRhoNode160Coeff2] using
    pole_rho_mul_0_2 rho (poleRhoScalar46Coeff0 a f) (poleRhoNode046Coeff0 a f) (poleRhoNode046Coeff1 a f) (poleRhoNode046Coeff2 a f)

theorem poleRhoNode161_eval (a f rho : ℝ) :
    poleRhoNode161 a f rho=((((poleRhoNode161Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode161Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode161Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode161Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode161Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode161Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode161Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode161Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode161Coeff8 a f)*(rho)^(8 : ℕ))))) := by
  unfold poleRhoNode161
  rw [poleRhoNode160_eval,poleRhoNode068_eval]
  simpa only [poleRhoNode161Coeff0,poleRhoNode161Coeff1,poleRhoNode161Coeff2,poleRhoNode161Coeff3,poleRhoNode161Coeff4,poleRhoNode161Coeff5,poleRhoNode161Coeff6,poleRhoNode161Coeff7,poleRhoNode161Coeff8] using
    pole_rho_mul_2_6 rho (poleRhoNode160Coeff0 a f) (poleRhoNode160Coeff1 a f) (poleRhoNode160Coeff2 a f) (poleRhoNode068Coeff0 a f) (poleRhoNode068Coeff1 a f) (poleRhoNode068Coeff2 a f) (poleRhoNode068Coeff3 a f) (poleRhoNode068Coeff4 a f) (poleRhoNode068Coeff5 a f) (poleRhoNode068Coeff6 a f)

theorem poleRhoNode162_eval (a f rho : ℝ) :
    poleRhoNode162 a f rho=((((poleRhoNode162Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode162Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode162Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode162Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode162Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode162Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode162Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode162Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode162Coeff8 a f)*(rho)^(8 : ℕ))))) := by
  unfold poleRhoNode162
  rw [poleRhoNode158_eval,poleRhoNode161_eval]
  simpa only [poleRhoNode162Coeff0,poleRhoNode162Coeff1,poleRhoNode162Coeff2,poleRhoNode162Coeff3,poleRhoNode162Coeff4,poleRhoNode162Coeff5,poleRhoNode162Coeff6,poleRhoNode162Coeff7,poleRhoNode162Coeff8] using
    pole_rho_add_8_8 rho (poleRhoNode158Coeff0 a f) (poleRhoNode158Coeff1 a f) (poleRhoNode158Coeff2 a f) (poleRhoNode158Coeff3 a f) (poleRhoNode158Coeff4 a f) (poleRhoNode158Coeff5 a f) (poleRhoNode158Coeff6 a f) (poleRhoNode158Coeff7 a f) (poleRhoNode158Coeff8 a f) (poleRhoNode161Coeff0 a f) (poleRhoNode161Coeff1 a f) (poleRhoNode161Coeff2 a f) (poleRhoNode161Coeff3 a f) (poleRhoNode161Coeff4 a f) (poleRhoNode161Coeff5 a f) (poleRhoNode161Coeff6 a f) (poleRhoNode161Coeff7 a f) (poleRhoNode161Coeff8 a f)

theorem poleRhoNode163_eval (a f rho : ℝ) :
    poleRhoNode163 a f rho=((((poleRhoNode163Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode163Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode163Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode163Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode163Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode163Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode163Coeff6 a f)*(rho)^(6 : ℕ)+((poleRhoNode163Coeff7 a f)*(rho)^(7 : ℕ)+(poleRhoNode163Coeff8 a f)*(rho)^(8 : ℕ))))) := by
  unfold poleRhoNode163
  rw [poleRhoNode155_eval,poleRhoNode162_eval]
  simpa only [poleRhoNode163Coeff0,poleRhoNode163Coeff1,poleRhoNode163Coeff2,poleRhoNode163Coeff3,poleRhoNode163Coeff4,poleRhoNode163Coeff5,poleRhoNode163Coeff6,poleRhoNode163Coeff7,poleRhoNode163Coeff8] using
    pole_rho_add_8_8 rho (poleRhoNode155Coeff0 a f) (poleRhoNode155Coeff1 a f) (poleRhoNode155Coeff2 a f) (poleRhoNode155Coeff3 a f) (poleRhoNode155Coeff4 a f) (poleRhoNode155Coeff5 a f) (poleRhoNode155Coeff6 a f) (poleRhoNode155Coeff7 a f) (poleRhoNode155Coeff8 a f) (poleRhoNode162Coeff0 a f) (poleRhoNode162Coeff1 a f) (poleRhoNode162Coeff2 a f) (poleRhoNode162Coeff3 a f) (poleRhoNode162Coeff4 a f) (poleRhoNode162Coeff5 a f) (poleRhoNode162Coeff6 a f) (poleRhoNode162Coeff7 a f) (poleRhoNode162Coeff8 a f)

theorem poleRhoInvariant5_eval (a f rho : ℝ) :
    poleRhoInvariant5 a f rho=(poleRhoInvariant5Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoInvariant5 poleRhoInvariant5Coeff0
  ring

theorem poleRhoNode165_eval (a f rho : ℝ) :
    poleRhoNode165 a f rho=((((poleRhoNode165Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode165Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode165Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode165Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode165Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode165Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode165Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode165Coeff7 a f)*(rho)^(7 : ℕ)))) := by
  unfold poleRhoNode165
  rw [poleRhoNode022_eval,poleRhoUpper5_eval]
  simpa only [poleRhoNode165Coeff0,poleRhoNode165Coeff1,poleRhoNode165Coeff2,poleRhoNode165Coeff3,poleRhoNode165Coeff4,poleRhoNode165Coeff5,poleRhoNode165Coeff6,poleRhoNode165Coeff7] using
    pole_rho_mul_3_4 rho (poleRhoNode022Coeff0 a f) (poleRhoNode022Coeff1 a f) (poleRhoNode022Coeff2 a f) (poleRhoNode022Coeff3 a f) (poleRhoUpper5Coeff0 a f) (poleRhoUpper5Coeff1 a f) (poleRhoUpper5Coeff2 a f) (poleRhoUpper5Coeff3 a f) (poleRhoUpper5Coeff4 a f)

theorem poleRhoNode166_eval (a f rho : ℝ) :
    poleRhoNode166 a f rho=((((poleRhoNode166Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode166Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode166Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode166Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode166Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode166Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode166Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode166Coeff7 a f)*(rho)^(7 : ℕ)))) := by
  unfold poleRhoNode166
  rw [poleRhoInvariant5_eval,poleRhoNode165_eval]
  simpa only [poleRhoNode166Coeff0,poleRhoNode166Coeff1,poleRhoNode166Coeff2,poleRhoNode166Coeff3,poleRhoNode166Coeff4,poleRhoNode166Coeff5,poleRhoNode166Coeff6,poleRhoNode166Coeff7] using
    pole_rho_mul_0_7 rho (poleRhoInvariant5Coeff0 a f) (poleRhoNode165Coeff0 a f) (poleRhoNode165Coeff1 a f) (poleRhoNode165Coeff2 a f) (poleRhoNode165Coeff3 a f) (poleRhoNode165Coeff4 a f) (poleRhoNode165Coeff5 a f) (poleRhoNode165Coeff6 a f) (poleRhoNode165Coeff7 a f)

theorem poleRhoScalar55_eval (a f rho : ℝ) :
    poleRhoScalar55 a f rho=(poleRhoScalar55Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar55 poleRhoScalar55Coeff0
  ring

theorem poleRhoNode168_eval (a f rho : ℝ) :
    poleRhoNode168 a f rho=(poleRhoNode168Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoNode168
  rw [poleRhoScalar55_eval,poleRhoOne_eval]
  simpa only [poleRhoNode168Coeff0] using
    pole_rho_mul_0_0 rho (poleRhoScalar55Coeff0 a f) (poleRhoOneCoeff0 a f)

theorem poleRhoNode169_eval (a f rho : ℝ) :
    poleRhoNode169 a f rho=((((poleRhoNode169Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode169Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode169Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode169Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode169Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode169Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode169Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode169Coeff7 a f)*(rho)^(7 : ℕ)))) := by
  unfold poleRhoNode169
  rw [poleRhoNode168_eval,poleRhoNode063_eval]
  simpa only [poleRhoNode169Coeff0,poleRhoNode169Coeff1,poleRhoNode169Coeff2,poleRhoNode169Coeff3,poleRhoNode169Coeff4,poleRhoNode169Coeff5,poleRhoNode169Coeff6,poleRhoNode169Coeff7] using
    pole_rho_mul_0_7 rho (poleRhoNode168Coeff0 a f) (poleRhoNode063Coeff0 a f) (poleRhoNode063Coeff1 a f) (poleRhoNode063Coeff2 a f) (poleRhoNode063Coeff3 a f) (poleRhoNode063Coeff4 a f) (poleRhoNode063Coeff5 a f) (poleRhoNode063Coeff6 a f) (poleRhoNode063Coeff7 a f)

theorem poleRhoScalar56_eval (a f rho : ℝ) :
    poleRhoScalar56 a f rho=(poleRhoScalar56Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar56 poleRhoScalar56Coeff0
  ring

theorem poleRhoNode171_eval (a f rho : ℝ) :
    poleRhoNode171 a f rho=((poleRhoNode171Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode171Coeff1 a f)*(rho)^(1 : ℕ)) := by
  unfold poleRhoNode171
  rw [poleRhoScalar56_eval,poleRhoBase_eval]
  simpa only [poleRhoNode171Coeff0,poleRhoNode171Coeff1] using
    pole_rho_mul_0_1 rho (poleRhoScalar56Coeff0 a f) (poleRhoBaseCoeff0 a f) (poleRhoBaseCoeff1 a f)

theorem poleRhoNode172_eval (a f rho : ℝ) :
    poleRhoNode172 a f rho=((((poleRhoNode172Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode172Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode172Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode172Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode172Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode172Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode172Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode172Coeff7 a f)*(rho)^(7 : ℕ)))) := by
  unfold poleRhoNode172
  rw [poleRhoNode171_eval,poleRhoNode068_eval]
  simpa only [poleRhoNode172Coeff0,poleRhoNode172Coeff1,poleRhoNode172Coeff2,poleRhoNode172Coeff3,poleRhoNode172Coeff4,poleRhoNode172Coeff5,poleRhoNode172Coeff6,poleRhoNode172Coeff7] using
    pole_rho_mul_1_6 rho (poleRhoNode171Coeff0 a f) (poleRhoNode171Coeff1 a f) (poleRhoNode068Coeff0 a f) (poleRhoNode068Coeff1 a f) (poleRhoNode068Coeff2 a f) (poleRhoNode068Coeff3 a f) (poleRhoNode068Coeff4 a f) (poleRhoNode068Coeff5 a f) (poleRhoNode068Coeff6 a f)

theorem poleRhoNode173_eval (a f rho : ℝ) :
    poleRhoNode173 a f rho=((((poleRhoNode173Coeff0 a f)*(rho)^(0 : ℕ)+(poleRhoNode173Coeff1 a f)*(rho)^(1 : ℕ))+((poleRhoNode173Coeff2 a f)*(rho)^(2 : ℕ)+(poleRhoNode173Coeff3 a f)*(rho)^(3 : ℕ)))+(((poleRhoNode173Coeff4 a f)*(rho)^(4 : ℕ)+(poleRhoNode173Coeff5 a f)*(rho)^(5 : ℕ))+((poleRhoNode173Coeff6 a f)*(rho)^(6 : ℕ)+(poleRhoNode173Coeff7 a f)*(rho)^(7 : ℕ)))) := by
  unfold poleRhoNode173
  rw [poleRhoNode169_eval,poleRhoNode172_eval]
  simpa only [poleRhoNode173Coeff0,poleRhoNode173Coeff1,poleRhoNode173Coeff2,poleRhoNode173Coeff3,poleRhoNode173Coeff4,poleRhoNode173Coeff5,poleRhoNode173Coeff6,poleRhoNode173Coeff7] using
    pole_rho_add_7_7 rho (poleRhoNode169Coeff0 a f) (poleRhoNode169Coeff1 a f) (poleRhoNode169Coeff2 a f) (poleRhoNode169Coeff3 a f) (poleRhoNode169Coeff4 a f) (poleRhoNode169Coeff5 a f) (poleRhoNode169Coeff6 a f) (poleRhoNode169Coeff7 a f) (poleRhoNode172Coeff0 a f) (poleRhoNode172Coeff1 a f) (poleRhoNode172Coeff2 a f) (poleRhoNode172Coeff3 a f) (poleRhoNode172Coeff4 a f) (poleRhoNode172Coeff5 a f) (poleRhoNode172Coeff6 a f) (poleRhoNode172Coeff7 a f)

theorem poleRhoInvariant6_eval (a f rho : ℝ) :
    poleRhoInvariant6 a f rho=(poleRhoInvariant6Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoInvariant6 poleRhoInvariant6Coeff0
  ring

theorem poleRhoNode175_eval (a f rho : ℝ) :
    poleRhoNode175 a f rho=(((poleRhoNode175Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode175Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode175Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoNode175Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode175Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoNode175Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode175Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoNode175
  rw [poleRhoNode022_eval,poleRhoCore4_eval]
  simpa only [poleRhoNode175Coeff0,poleRhoNode175Coeff1,poleRhoNode175Coeff2,poleRhoNode175Coeff3,poleRhoNode175Coeff4,poleRhoNode175Coeff5,poleRhoNode175Coeff6] using
    pole_rho_mul_3_3 rho (poleRhoNode022Coeff0 a f) (poleRhoNode022Coeff1 a f) (poleRhoNode022Coeff2 a f) (poleRhoNode022Coeff3 a f) (poleRhoCore4Coeff0 a f) (poleRhoCore4Coeff1 a f) (poleRhoCore4Coeff2 a f) (poleRhoCore4Coeff3 a f)

theorem poleRhoNode176_eval (a f rho : ℝ) :
    poleRhoNode176 a f rho=(((poleRhoNode176Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode176Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode176Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoNode176Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode176Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoNode176Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode176Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoNode176
  rw [poleRhoInvariant6_eval,poleRhoNode175_eval]
  simpa only [poleRhoNode176Coeff0,poleRhoNode176Coeff1,poleRhoNode176Coeff2,poleRhoNode176Coeff3,poleRhoNode176Coeff4,poleRhoNode176Coeff5,poleRhoNode176Coeff6] using
    pole_rho_mul_0_6 rho (poleRhoInvariant6Coeff0 a f) (poleRhoNode175Coeff0 a f) (poleRhoNode175Coeff1 a f) (poleRhoNode175Coeff2 a f) (poleRhoNode175Coeff3 a f) (poleRhoNode175Coeff4 a f) (poleRhoNode175Coeff5 a f) (poleRhoNode175Coeff6 a f)

theorem poleRhoScalar66_eval (a f rho : ℝ) :
    poleRhoScalar66 a f rho=(poleRhoScalar66Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoScalar66 poleRhoScalar66Coeff0
  ring

theorem poleRhoNode178_eval (a f rho : ℝ) :
    poleRhoNode178 a f rho=(poleRhoNode178Coeff0 a f)*(rho)^(0 : ℕ) := by
  unfold poleRhoNode178
  rw [poleRhoScalar66_eval,poleRhoOne_eval]
  simpa only [poleRhoNode178Coeff0] using
    pole_rho_mul_0_0 rho (poleRhoScalar66Coeff0 a f) (poleRhoOneCoeff0 a f)

theorem poleRhoNode179_eval (a f rho : ℝ) :
    poleRhoNode179 a f rho=(((poleRhoNode179Coeff0 a f)*(rho)^(0 : ℕ)+((poleRhoNode179Coeff1 a f)*(rho)^(1 : ℕ)+(poleRhoNode179Coeff2 a f)*(rho)^(2 : ℕ)))+(((poleRhoNode179Coeff3 a f)*(rho)^(3 : ℕ)+(poleRhoNode179Coeff4 a f)*(rho)^(4 : ℕ))+((poleRhoNode179Coeff5 a f)*(rho)^(5 : ℕ)+(poleRhoNode179Coeff6 a f)*(rho)^(6 : ℕ)))) := by
  unfold poleRhoNode179
  rw [poleRhoNode178_eval,poleRhoNode068_eval]
  simpa only [poleRhoNode179Coeff0,poleRhoNode179Coeff1,poleRhoNode179Coeff2,poleRhoNode179Coeff3,poleRhoNode179Coeff4,poleRhoNode179Coeff5,poleRhoNode179Coeff6] using
    pole_rho_mul_0_6 rho (poleRhoNode178Coeff0 a f) (poleRhoNode068Coeff0 a f) (poleRhoNode068Coeff1 a f) (poleRhoNode068Coeff2 a f) (poleRhoNode068Coeff3 a f) (poleRhoNode068Coeff4 a f) (poleRhoNode068Coeff5 a f) (poleRhoNode068Coeff6 a f)

end LeanVerification.PositiveDCompletion
