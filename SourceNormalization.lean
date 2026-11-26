import LeanVerification.PositiveDCompletion.SignedModelAlgebra
import LeanVerification.PositiveDCompletion.SourceFractionAlgebra

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

def sourceB (a f rho : ℝ) : ℝ := 2*(f-a)*(1-f)*(1-rho)
def sourceH (a f rho : ℝ) : ℝ := (f-a)*(1-rho)
def sourceM (a f rho : ℝ) : ℝ := (1+a)*(f-a*rho)
def sourceC (a f rho : ℝ) : ℝ := a*rho*(1-a*f)
def sourceFlow (a f rho : ℝ) : ℝ :=
  (1+a)*rho*(a*(1+a)*(f-a*rho)*(1-f)+2*(1-a*f)*(f-a))
def sourceT (a f rho w : ℝ) : ℝ :=
  sourceB a f rho*(1+f)^3*(modelG a rho)^3-
    weakNum00 a f rho*(1+f)^2*modelG a rho*w-
    weakNum01 a f rho*(1+f)*modelG a rho*w^2-
    weakNum02 a f rho*w^3-weakNum03 a f rho*w^4
def sourceRZero (a f rho : ℝ) : ℝ :=
  weakNum09 a f rho-a*(a+1)*sourceH a f rho*(1+f)*modelG a rho
def sourcePole (a f rho w : ℝ) : ℝ :=
  (2*sourceM a f rho*modelG a rho*(1+f)^2+
    6*sourceM a f rho*sourceC a f rho*(1+f)+3*sourceFlow a f rho*(1+f))*w+
  (8*sourceM a f rho*sourceC a f rho*(1+f)+3*f*sourceFlow a f rho)*w^2
def sourceV (a f rho w : ℝ) : ℝ :=
  weakNum04 a f rho*modelG a rho*(1+f)^3*w+
    2*weakNum05 a f rho*modelG a rho*(1+f)^2*w^2+
    weakNum06 a f rho*(1+f)*w^3+2*weakNum07 a f rho*w^4+a*weakNum08 a f rho*w^5+
    a*(1+f)*sourceH a f rho*sourceM a f rho*
      (-sourceB a f rho*(modelG a rho)^3*(1+f)^3*w+
       weakNum00 a f rho*modelG a rho*(1+f)^2*w^2+
       weakNum01 a f rho*modelG a rho*(1+f)*w^3+
       weakNum02 a f rho*w^4+weakNum03 a f rho*w^5)
def sourceRXCleared (a f rho w : ℝ) : ℝ :=
  a*sourceH a f rho*(1+f)*sourceT a f rho w*(transportN a f rho w)^2+
    sourceT a f rho w*(1+f+f*w)*sourceRZero a f rho*transportN a f rho w+
    a*sourceH a f rho*sourceT a f rho w*sourcePole a f rho w+
    sourceV a f rho w*transportN a f rho w

namespace SignedRegular
variable {a f rho w : ℝ} (h : SignedRegular a f rho)
include h

theorem sourceB_ne : sourceB a f rho≠0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h.f_a_ne) h.f_one_ne) h.rho_one_ne

theorem sourceH_ne : sourceH a f rho≠0 := mul_ne_zero h.f_a_ne h.rho_one_ne

theorem modelPsi_eq_source :
    modelPsi a f rho w=sourceT a f rho w/(sourceB a f rho*(1+f)^3*(modelG a rho)^3) := by
  have he := signed_psi_fraction (sourceB a f rho) (1+f) (modelG a rho)
    (weakNum00 a f rho) (weakNum01 a f rho) (weakNum02 a f rho) (weakNum03 a f rho)
    w h.sourceB_ne h.j_ne h.g_ne
  convert he using 1 <;>
    simp only [modelPsi,compactPsi,modelAlpha1,modelAlpha2,modelAlpha3,modelAlpha4,sourceB,sourceT] <;> ring

theorem modelRZero_eq_source :
    modelRZero a f rho-1=sourceRZero a f rho/(a*sourceH a f rho*(1+f)*modelG a rho) := by
  convert signed_rzero_fraction a (f-a) (1-rho) (1+f) (modelG a rho)
    (weakNum09 a f rho) h.a_ne h.f_a_ne h.rho_one_ne h.j_ne h.g_ne using 1 <;>
    simp only [modelRZero,sourceRZero,sourceH] <;> ring

theorem modelPole_eq_source :
    compactPoleNumerator (modelM a f rho) (modelEll a f rho) (modelSigma f)
      (modelPoleFlow a f rho) w=sourcePole a f rho w/((modelG a rho)^2*(1+f)^3) := by
  have he := signed_pole_fraction (1+f) (modelG a rho) (sourceM a f rho)
    (sourceC a f rho) (sourceFlow a f rho) f w h.j_ne h.g_ne
  convert he using 1 <;>
    simp only [compactPoleNumerator,modelM,modelEll,modelSigma,modelPoleFlow,sourceM,sourceC,sourceFlow,sourcePole] <;> ring

theorem modelV_eq_source :
    compactSourceNumerator (modelV1 a f rho) (modelV2 a f rho) (modelV3 a f rho)
      (modelV4 a f rho) (modelV5 a f rho) w=
    sourceV a f rho w/(a*sourceB a f rho*(modelG a rho)^4*(1+f)^5*sourceH a f rho) := by
  exact signed_source_values_fraction a (f-a) (1-f) (1-rho) (1+f) (modelG a rho)
    (sourceM a f rho) (weakNum00 a f rho) (weakNum01 a f rho) (weakNum02 a f rho)
    (weakNum03 a f rho) (weakNum04 a f rho) (weakNum05 a f rho) (weakNum06 a f rho)
    (weakNum07 a f rho) (weakNum08 a f rho) w
    h.a_ne h.f_a_ne h.f_one_ne h.rho_one_ne h.j_ne h.g_ne

theorem modelRX_eq_source (hw : 1+w≠0) (hn : transportN a f rho w≠0)
    (hPsi : modelPsi a f rho w≠0) :
    modelF a f rho w*modelR a f rho w=
      (1+a)*sourceRXCleared a f rho w/
        (4*a*sourceH a f rho*(1+f)*(1+w)*modelA a f rho*(transportN a f rho w)^5) := by
  have ht : sourceT a f rho w≠0 := by
    intro hz
    apply hPsi
    rw [h.modelPsi_eq_source,hz,zero_div]
  have hf0 : modelFZero a f rho=(1+a)*sourceB a f rho/(4*modelA a f rho) := by
    unfold modelFZero sourceB
    ring
  have hsigma : 1+modelSigma f*w=(1+f+f*w)/(1+f) := by
    unfold modelSigma
    field_simp [h.j_ne]
    <;> ring
  unfold modelF modelR modelLambda modelSource compactSource
  change (modelFZero a f rho*modelPsi a f rho w/((1+w)*(modelL a f rho w)^3))*
    (1+((1+modelSigma f*w)/modelL a f rho w)*(modelRZero a f rho-1)+
      (compactPoleNumerator (modelM a f rho) (modelEll a f rho) (modelSigma f)
        (modelPoleFlow a f rho) w/(modelL a f rho w)^2+
       compactSourceNumerator (modelV1 a f rho) (modelV2 a f rho) (modelV3 a f rho)
        (modelV4 a f rho) (modelV5 a f rho) w/(modelL a f rho w*modelPsi a f rho w)))= _
  rw [hf0,hsigma,h.modelPsi_eq_source,h.modelL_transportN,h.modelRZero_eq_source,
    h.modelPole_eq_source,h.modelV_eq_source]
  convert signed_source_fraction_assembly a (sourceB a f rho) (sourceH a f rho) (1+f)
    (modelG a rho) (modelA a f rho) (1+w) (transportN a f rho w) (1+a)
    (sourceT a f rho w) (1+f+f*w) (sourceRZero a f rho) (sourcePole a f rho w)
    (sourceV a f rho w) h.a_ne h.sourceB_ne h.sourceH_ne h.j_ne h.g_ne h.A_ne hw hn ht using 1 <;>
    dsimp only [sourceRXCleared] <;> ring

end SignedRegular
end LeanVerification.PositiveDCompletion
