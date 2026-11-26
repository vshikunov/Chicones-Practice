import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

theorem signed_psi_fraction (B j g n0 n1 n2 n3 w : ℝ)
    (hB : B≠0) (hj : j≠0) (hg : g≠0) :
    1-n0/(B*j*g^2)*w-n1/(B*j^2*g^2)*w^2-
      n2/(B*j^3*g^3)*w^3-n3/(B*j^3*g^3)*w^4 =
    (B*j^3*g^3-n0*j^2*g*w-n1*j*g*w^2-n2*w^3-n3*w^4)/(B*j^3*g^3) := by
  field_simp (disch := simp [hB,hj,hg]) [hB,hj,hg]
  ring

theorem signed_source_fraction_assembly
    (a B H j g A Z N m T b r p s : ℝ)
    (ha : a≠0) (hB : B≠0) (hH : H≠0) (hj : j≠0) (hg : g≠0)
    (hA : A≠0) (hZ : Z≠0) (hN : N≠0) (hT : T≠0) :
    (m*B/(4*A)*(T/(B*j^3*g^3))/(Z*(N/(g*j))^3))*
      (1+(b/j)/(N/(g*j))*(r/(a*H*j*g))+
        p/(g^2*j^3)/(N/(g*j))^2+
        (s/(a*B*g^4*j^5*H))/((N/(g*j))*(T/(B*j^3*g^3)))) =
    m*(a*H*j*T*N^2+T*b*r*N+a*H*T*p+s*N)/(4*a*H*j*Z*A*N^5) := by
  field_simp (disch := simp [ha,hB,hH,hj,hg,hA,hZ,hN,hT])
    [ha,hB,hH,hj,hg,hA,hZ,hN,hT]
  ring

theorem signed_pole_fraction (j g m c t f w : ℝ) (hj : j≠0) (hg : g≠0) :
    (2*(m/(g*j))+6*(m/(g*j))*(c/(g*j))+3*(t/(g^2*j^2)))*w+
      (8*(m/(g*j))*(c/(g*j))+3*(f/j)*(t/(g^2*j^2)))*w^2 =
    ((2*m*g*j^2+6*m*c*j+3*t*j)*w+(8*m*c*j+3*f*t)*w^2)/(g^2*j^3) := by
  field_simp (disch := simp [hj,hg]) [hj,hg]
  ring

theorem signed_rzero_fraction (a q r j g n : ℝ)
    (ha : a≠0) (hq : q≠0) (hr : r≠0) (hj : j≠0) (hg : g≠0) :
    n/(a*q*j*r*g)-a-1=(n-a*(a+1)*q*r*j*g)/(a*(q*r)*j*g) := by
  field_simp (disch := simp [ha,hq,hr,hj,hg]) [ha,hq,hr,hj,hg]
  ring

theorem signed_source_values_fraction
    (a q v r j g m n0 n1 n2 n3 n4 n5 n6 n7 n8 w : ℝ)
    (ha : a≠0) (hq : q≠0) (hv : v≠0) (hr : r≠0) (hj : j≠0) (hg : g≠0) :
    (n4/(2*a*q^2*v*j^2*r^2*g^3)-m/(g*j))*w+
    (n5/(a*q^2*v*j^3*r^2*g^3)+(m/(g*j))*(n0/(2*q*v*j*r*g^2)))*w^2+
    (n6/(2*a*q^2*v*j^4*r^2*g^4)+(m/(g*j))*(n1/(2*q*v*j^2*r*g^2)))*w^3+
    (n7/(a*q^2*v*j^5*r^2*g^4)+(m/(g*j))*(n2/(2*q*v*j^3*r*g^3)))*w^4+
    (n8/(2*q^2*v*j^5*r^2*g^4)+(m/(g*j))*(n3/(2*q*v*j^3*r*g^3)))*w^5 =
    (n4*g*j^3*w+2*n5*g*j^2*w^2+n6*j*w^3+2*n7*w^4+a*n8*w^5+
      a*j*(q*r)*m*(-(2*q*v*r)*g^3*j^3*w+n0*g*j^2*w^2+
        n1*g*j*w^3+n2*w^4+n3*w^5))/(a*(2*q*v*r)*g^4*j^5*(q*r)) := by
  field_simp (disch := simp [ha,hq,hv,hr,hj,hg]) [ha,hq,hv,hr,hj,hg]
  ring

end LeanVerification.PositiveDCompletion
