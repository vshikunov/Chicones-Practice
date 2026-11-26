import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

theorem source_coeff_assembly (a f H M C R p1 p2 w t0 t1 t2 t3 t4 v0 v1 v2 v3 v4 v5 : ℝ) :
    a*H*(1+f)*(((t0*w^0+t1*w^1)+(t2*w^2+(t3*w^3+t4*w^4))))*(M+C*w)^2+(((t0*w^0+t1*w^1)+(t2*w^2+(t3*w^3+t4*w^4))))*(1+f+f*w)*R*(M+C*w)+a*H*(((t0*w^0+t1*w^1)+(t2*w^2+(t3*w^3+t4*w^4))))*(p1*w+p2*w^2)+(((v0*w^0+(v1*w^1+v2*w^2))+(v3*w^3+(v4*w^4+v5*w^5))))*(M+C*w)=
    (((a*H*(1+f)*(t0*M^2+2*(0 : ℝ)*M*C+(0 : ℝ)*C^2)+R*((1+f)*M*t0+((1+f)*C+f*M)*(0 : ℝ)+f*C*(0 : ℝ))+a*H*(p1*(0 : ℝ)+p2*(0 : ℝ))+M*v0+C*(0 : ℝ))*w^0+((a*H*(1+f)*(t1*M^2+2*t0*M*C+(0 : ℝ)*C^2)+R*((1+f)*M*t1+((1+f)*C+f*M)*t0+f*C*(0 : ℝ))+a*H*(p1*t0+p2*(0 : ℝ))+M*v1+C*v0)*w^1+(a*H*(1+f)*(t2*M^2+2*t1*M*C+t0*C^2)+R*((1+f)*M*t2+((1+f)*C+f*M)*t1+f*C*t0)+a*H*(p1*t1+p2*t0)+M*v2+C*v1)*w^2))+(((a*H*(1+f)*(t3*M^2+2*t2*M*C+t1*C^2)+R*((1+f)*M*t3+((1+f)*C+f*M)*t2+f*C*t1)+a*H*(p1*t2+p2*t1)+M*v3+C*v2)*w^3+(a*H*(1+f)*(t4*M^2+2*t3*M*C+t2*C^2)+R*((1+f)*M*t4+((1+f)*C+f*M)*t3+f*C*t2)+a*H*(p1*t3+p2*t2)+M*v4+C*v3)*w^4)+((a*H*(1+f)*((0 : ℝ)*M^2+2*t4*M*C+t3*C^2)+R*((1+f)*M*(0 : ℝ)+((1+f)*C+f*M)*t4+f*C*t3)+a*H*(p1*t4+p2*t3)+M*v5+C*v4)*w^5+(a*H*(1+f)*((0 : ℝ)*M^2+2*(0 : ℝ)*M*C+t4*C^2)+R*((1+f)*M*(0 : ℝ)+((1+f)*C+f*M)*(0 : ℝ)+f*C*t4)+a*H*(p1*(0 : ℝ)+p2*t4)+M*(0 : ℝ)+C*v5)*w^6))) := by ring

theorem source_t_coeff_assembly (b j g n0 n1 n2 n3 w : ℝ) :
    b*j^3*g^3-n0*j^2*g*w-n1*j*g*w^2-n2*w^3-n3*w^4=
    (((b*j^3*g^3)*w^0+(-n0*j^2*g)*w^1)+((-n1*j*g)*w^2+((-n2)*w^3+(-n3)*w^4))) := by ring

theorem source_v_coeff_assembly (a b j g H M n0 n1 n2 n3 n4 n5 n6 n7 n8 w : ℝ) :
    n4*g*j^3*w+2*n5*g*j^2*w^2+n6*j*w^3+2*n7*w^4+a*n8*w^5+a*j*H*M*(-b*g^3*j^3*w+n0*g*j^2*w^2+n1*g*j*w^3+n2*w^4+n3*w^5)=
    ((((0 : ℝ))*w^0+((n4*g*j^3-a*j*H*M*b*g^3*j^3)*w^1+(2*n5*g*j^2+a*j*H*M*n0*g*j^2)*w^2))+((n6*j+a*j*H*M*n1*g*j)*w^3+((2*n7+a*j*H*M*n2)*w^4+(a*n8+a*j*H*M*n3)*w^5))) := by ring

end LeanVerification.PositiveDCompletion
