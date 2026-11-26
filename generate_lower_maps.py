#!/usr/bin/env python3
"""Emit fixed-degree homogeneous coordinate identities for the lower cone."""
import re
import argparse,json,math
from pathlib import Path
from generate_upper_certificates import balanced


def coeff(d,j,values,a='a',f='f'):
    return balanced([f'({math.comb(k,j)} : ℝ)*{values[k]}*{a}^{k-j}*{f}^{d-k}' for k in range(j,d+1)])


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path)
    args=parser.parse_args();root=Path(__file__).resolve().parent;out=args.output or root
    data=json.loads((root/'data/lower_certificates.json').read_text())
    header='''noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000

'''
    text='import LeanVerification.PositiveDCompletion.LowerCoordinates\n\n'+header
    for d in sorted(set(e['rho_degree'] for e in data)):
        ls=[f'c{k}' for k in range(d+1)]
        left=balanced([f'{ls[k]}*((a*d0+w*u)/(f*d0))^{k}' for k in range(d+1)])
        right=balanced([f'd0^{d-j}*w^{j}*({coeff(d,j,ls)})*u^{j}' for j in range(d+1)])
        text+=f'theorem lower_homogeneous_{d} (a f d0 w u '+ ' '.join(ls)+f' : ℝ) (hf : f≠0) (hd : d0≠0) :\n    (f*d0)^{d}*({left})={right} := by\n  field_simp (disch := simp [hf,hd]) [hf,hd]\n  ring\n\n'
    text+='end LeanVerification.PositiveDCompletion\n';(out/'LowerHomogeneous.lean').write_text(re.sub(r'\^(\d+)',lambda m: '^('+m.group(1)+' : ℕ)',text))
    for index,e in enumerate(data):
        d=e['rho_degree'];pa,pt,p1=[k for _,k in e['factors']]
        cn=[f'c{k}' for k in range(d+1)]
        rhs=[];lhs=[]
        for j,c in enumerate(e['core_coefficients']):
            ea,et,e1=c['powers'];aa,tt,ll=c['atom_powers']
            lhs.append(f'(a^2*t^2*b)^{d-j}*((1-t)^2*g)^{j}*(x^{ea}*t^{et}*(1-t)^{e1}*c{j})*u^{j}')
            rhs.append(f'(x^{aa}*a^{2*(d-j)}*t^{tt}*(1-t)^{ll}*b^{d-j}*g^{j}*c{j})*u^{j}')
        factor=f'lower_factor_{index:02d}'
        text=f'import LeanVerification.PositiveDCompletion.LowerPolynomial{index:02d}\nimport LeanVerification.PositiveDCompletion.LowerHomogeneous\n\n'+header
        text+=f'theorem {factor} (a x t b g u '+ ' '.join(cn)+f' : ℝ) :\n    {balanced(lhs)}=x^{pa}*t^{pt}*(1-t)^{p1}*({balanced(rhs)}) := by ring\n\n'
        name=f'lowerNum{index:02d}';atom=f'lowerAtom{index:02d}'
        text+=f'theorem {name}_map {{x t u : ℝ}} (hx : 0<x) (hxu : x<1) (ht : 0<t) (htu : t<1) :\n    (lowerRhoDen (1+2*x) t)^{d}*{name} (1+2*x) (lowerCubeF (1+2*x) t)\n      (lowerRhoNum (1+2*x) t u/lowerRhoDen (1+2*x) t)=\n    (2*x)^{pa}*t^{pt}*(1-t)^{p1}*{atom} x t u := by\n'
        text+='  have ha : 1<1+2*x := by linarith\n  have hau : 1+2*x<3 := by linarith\n  have hB := lowerCubeB_pos ha hau ht htu\n  have ha0 : 0<1+2*x := by linarith\n  have hF : 0<lowerCubeF (1+2*x) t := by\n    unfold lowerCubeF\n    have hx0 : 0<(1+2*x)-1 := by linarith\n    positivity\n  have hD : 0<lowerCubeD (1+2*x) t := by\n    unfold lowerCubeD\n    positivity\n'
        args=' '.join(f'({name}Coeff{k} (1+2*x) (lowerCubeF (1+2*x) t))' for k in range(d+1))
        text+=f'  have he := lower_homogeneous_{d} (1+2*x) (lowerCubeF (1+2*x) t)\n    (lowerCubeD (1+2*x) t) ((1-t)^2*lowerCubeG (1+2*x) t) u\n    {args} hF.ne\' hD.ne\'\n'
        text+='  rw ['+','.join(f'lowerCore{index:02d}Coeff{k}_map' for k in range(d+1))+'] at he\n'
        text+='  rw [show (1+2*x)-1=2*x by ring] at he\n'
        text+=f'  have hf := {factor} (1+2*x) (2*x) t (lowerCubeB (1+2*x) t) (lowerCubeG (1+2*x) t) u\n    '+ ' '.join(f'(lowerCore{index:02d}Coeff{k} (1+2*x) t)' for k in range(d+1))+'\n'
        text+=f'  change _=(2*x)^{pa}*t^{pt}*(1-t)^{p1}*{atom} x t u at hf\n'
        text+='  rw [←hf]\n  simpa only [lowerRhoDen,lowerRhoNum,lowerCubeD,'+name+'] using he\n\n'
        text+='end LeanVerification.PositiveDCompletion\n';(out/f'LowerMap{index:02d}.lean').write_text(re.sub(r'\^(\d+)',lambda m: '^('+m.group(1)+' : ℕ)',text))
    print('Emitted generic homogeneous identities and ten lower coordinate maps')


if __name__=='__main__':main()
