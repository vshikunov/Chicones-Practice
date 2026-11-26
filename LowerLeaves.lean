import LeanVerification.PositiveDCompletion.PoleSigns
import LeanVerification.PositiveDCompletion.SecantGeometry
import LeanVerification.PositiveDCompletion.LowerLeafEquality00
import LeanVerification.PositiveDCompletion.LowerPositivity00
import LeanVerification.PositiveDCompletion.LowerLeafEquality01
import LeanVerification.PositiveDCompletion.LowerPositivity01
import LeanVerification.PositiveDCompletion.LowerLeafEquality02
import LeanVerification.PositiveDCompletion.LowerPositivity02
import LeanVerification.PositiveDCompletion.LowerLeafEquality03
import LeanVerification.PositiveDCompletion.LowerPositivity03
import LeanVerification.PositiveDCompletion.LowerLeafEquality04
import LeanVerification.PositiveDCompletion.LowerPositivity04
import LeanVerification.PositiveDCompletion.LowerLeafEquality05
import LeanVerification.PositiveDCompletion.LowerPositivity05
import LeanVerification.PositiveDCompletion.LowerLeafEquality06
import LeanVerification.PositiveDCompletion.LowerPositivity06
import LeanVerification.PositiveDCompletion.LowerLeafEquality07
import LeanVerification.PositiveDCompletion.LowerPositivity07
import LeanVerification.PositiveDCompletion.LowerLeafEquality08
import LeanVerification.PositiveDCompletion.LowerPositivity08
import LeanVerification.PositiveDCompletion.LowerLeafEquality09
import LeanVerification.PositiveDCompletion.LowerPositivity09

noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion

theorem lower_leaf_signs {a f rho : ℝ} (ha : 1<a) (hau : a<3)
    (hf : 1<f) (hfa : f<a) (hr : a/f<rho) (hru : rho<lowerEnvelope a f) :
    LeafSigns (-1) a f rho := by
  constructor
  · have hp := lowerNum00_pos ha hau hf hfa hr hru
    rw [lowerNum00_eq_upper] at hp
    simpa only [neg_one_mul] using hp
  · have hp := lowerNum01_pos ha hau hf hfa hr hru
    rw [lowerNum01_eq_upper] at hp
    simpa only [neg_one_mul] using hp
  · have hp := lowerNum02_pos ha hau hf hfa hr hru
    rw [lowerNum02_eq_upper] at hp
    simpa only [neg_one_mul] using hp
  · have hp := lowerNum03_pos ha hau hf hfa hr hru
    rw [lowerNum03_eq_upper] at hp
    simpa only [neg_one_mul] using hp
  · have hp := lowerNum04_pos ha hau hf hfa hr hru
    rw [lowerNum04_eq_upper] at hp
    simpa only [neg_one_mul] using hp
  · have hp := lowerNum05_pos ha hau hf hfa hr hru
    rw [lowerNum05_eq_upper] at hp
    simpa only [neg_one_mul] using hp
  · have hp := lowerNum06_pos ha hau hf hfa hr hru
    rw [lowerNum06_eq_upper] at hp
    simpa only [neg_one_mul] using hp
  · have hp := lowerNum07_pos ha hau hf hfa hr hru
    rw [lowerNum07_eq_upper] at hp
    simpa only [neg_one_mul] using hp
  · have hp := lowerNum08_pos ha hau hf hfa hr hru
    rw [lowerNum08_eq_upper] at hp
    simpa only [neg_one_mul] using hp
  · have hp := lowerNum09_pos ha hau hf hfa hr hru
    rw [lowerNum09_eq_upper] at hp
    simpa only [neg_one_mul] using hp

theorem actual_lower_pole_signs {a q : ℝ} (ha : 1<a) (hau : a<3) (hq : 0<q) :
    PoleCoefficientSigns a (secantF a q) (secantRho a q) := by
  obtain ⟨hf,hfa,hr,hru⟩ := actual_lower_cone ha hau hq
  exact lower_pole_coefficient_signs ha hf hfa (secant_lower_bounds ha hq).2.2
    (lower_leaf_signs ha hau hf hfa hr hru)

end LeanVerification.PositiveDCompletion
