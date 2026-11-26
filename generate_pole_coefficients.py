#!/usr/bin/env python3
"""Emit signed-pole polynomial data and exact coefficient identities."""
import re
import argparse,json,math
from pathlib import Path
import sympy as sp
from generate_upper_certificates import balanced


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path)
    args=parser.parse_args();root=Path(__file__).resolve().parent;out=args.output or root
    data=json.loads((root/'data/source_coefficients.json').read_text())
    upper=json.loads((root/'data/upper_certificates.json').read_text())
    a,f,rho=sp.symbols('a f rho');leaves={}
    for i,e in enumerate(upper):
        expr=sp.Poly.from_dict({tuple(m):c for m,c in e['num']},(a,f,rho)).as_expr()
        leaves[expr]=f'(upperNum{i:02d} a f rho)';leaves[-expr]=f'(-upperNum{i:02d} a f rho)'
    cores={}
    def lean(e,top=False):
        if e in leaves:return leaves[e]
        if not top and e.is_Add and len(e.args)>3:
            if e not in cores:cores[e]=f'poleCore{len(cores):02d}'
            return f'({cores[e]} a f rho)'
        if e.is_Integer:return str(e) if e>=0 else f'({e})'
        if e.is_Symbol:return str(e)
        if e.is_Add:return balanced([lean(z) for z in e.args])
        if e.is_Mul:return balanced([lean(z) for z in e.args],'*')
        if e.is_Pow:return f'({lean(e.base)})^{int(e.exp)}'
        raise ValueError(e)
    header='''noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 64000000
set_option maxRecDepth 60000

'''
    text=''.join(f'import LeanVerification.PositiveDCompletion.UpperPolynomial{i:02d}'+('Data' if i>=8 else '')+'\n' for i in range(10))
    text+='import LeanVerification.PositiveDCompletion.SourceCoefficientData\nimport LeanVerification.PositiveDCompletion.PolynomialComparison\n\n'+header
    body=''
    pole={key:[sp.sympify(e) for e in data[key+'_pole']] for key in ['phi','rx']}
    for key in ['phi','rx']:
        for i,expr in enumerate(data[key+'_pole']):
            body+=f'def {key}PoleCoeff{i} (a f rho : ℝ) : ℝ := {lean(sp.sympify(expr))}\n\n'
    for i,expr in enumerate(data['comparisons']):
        body+=f'def poleComparison{i} (a f rho : ℝ) : ℝ := {lean(sp.sympify(expr))}\n\n'
    def factors(e):
        c,values=e.as_coeff_Mul();fs={}
        for v in sp.Mul.make_args(values):
            b,k=v.as_base_exp();fs[b]=fs.get(b,0)+int(k)
        return c,fs
    comparisons=[]
    for i,expr in enumerate(data['comparisons']):
        aa=-pole['phi'][4]*pole['rx'][i+2];bb=pole['rx'][6]*pole['phi'][i];cc=sp.sympify(expr)
        fact=[factors(e) for e in [aa,bb,cc]]
        common={b:min(f.get(b,0) for _,f in fact) for b in fact[0][1]}
        common={b:k for b,k in common.items() if k}
        g=sp.Mul(*[b**k for b,k in common.items()])
        values=[c*sp.Mul(*[b**(k-common.get(b,0)) for b,k in f.items()]) for c,f in fact]
        assert sp.Poly(values[0]+values[1]-values[2],a,f,rho).is_zero
        comparisons.append(values)
        for part,val in zip(['Common','Left','Right','Target'],[g]+values):
            body+=f'def poleComparison{part}{i} (a f rho : ℝ) : ℝ := {lean(val)}\n\n'
    text+=''.join(f'def {name} (a f rho : ℝ) : ℝ := {lean(expr,top=True)}\n\n' for expr,name in list(cores.items()))
    text+=body+'end LeanVerification.PositiveDCompletion\n';(out/'PoleCoefficientData.lean').write_text(re.sub(r'\^(\d+)',lambda m: '^('+m.group(1)+' : ℕ)',text))
    expands=[f'upperNum{i:02d}' for i in range(10)]+[f'upperNum{i:02d}Coeff{k}' for i in range(3,10) for k in range(max(m[2] for m,c in upper[i]['num'])+1)]+list(cores.values())
    for key in ['phi','rx']:
        d=len(data[key])-1
        for j in range(d+1):
            rhs=balanced([f'({math.comb(i,j)} : ℝ)*(-1 : ℝ)^{i}*(sourceBase a f rho)^{i-j}*(sourceC a f rho)^{d-i}*{key}NumCoeff{i} a f rho' for i in range(j,d+1)])
            text='import LeanVerification.PositiveDCompletion.PoleCoefficientData\n\n'+header
            text+=f'theorem {key}_pole_coefficient_{j} (a f rho : ℝ) :\n    {key}PoleCoeff{j} a f rho={rhs} := by\n  simp only ['+','.join([f'{key}PoleCoeff{j}']+[f'{key}NumCoeff{i}' for i in range(j,d+1)]+expands+['sourceBase','sourceC','modelG'])+']\n  ring\n\nend LeanVerification.PositiveDCompletion\n'
            (out/f'{key.title()}PoleCoefficient{j}.lean').write_text(re.sub(r'\^(\d+)',lambda m: '^('+m.group(1)+' : ℕ)',text))
    for i in range(4):
        text='import LeanVerification.PositiveDCompletion.PoleCoefficientData\n\n'+header
        text+=f'theorem pole_comparison_reduced_{i} (a f rho : ℝ) :\n    poleComparisonLeft{i} a f rho+poleComparisonRight{i} a f rho=poleComparisonTarget{i} a f rho := by\n  simp only ['+','.join([f'poleComparison{part}{i}' for part in ['Left','Right','Target']]+expands)+']\n  ring\n\n'
        text+=f'theorem pole_comparison_identity_{i} (a f rho : ℝ) :\n    -phiPoleCoeff4 a f rho*rxPoleCoeff{i+2} a f rho+rxPoleCoeff6 a f rho*phiPoleCoeff{i} a f rho=poleComparison{i} a f rho := by\n'
        for hn,left,right,defs in [
            ('ha',f'-phiPoleCoeff4 a f rho*rxPoleCoeff{i+2} a f rho',f'poleComparisonCommon{i} a f rho*poleComparisonLeft{i} a f rho',['phiPoleCoeff4',f'rxPoleCoeff{i+2}',f'poleComparisonCommon{i}',f'poleComparisonLeft{i}']),
            ('hb',f'rxPoleCoeff6 a f rho*phiPoleCoeff{i} a f rho',f'poleComparisonCommon{i} a f rho*poleComparisonRight{i} a f rho',['rxPoleCoeff6',f'phiPoleCoeff{i}',f'poleComparisonCommon{i}',f'poleComparisonRight{i}']),
            ('hc',f'poleComparisonCommon{i} a f rho*poleComparisonTarget{i} a f rho',f'poleComparison{i} a f rho',[f'poleComparisonCommon{i}',f'poleComparisonTarget{i}',f'poleComparison{i}'])]:
            text+=f'  have {hn} : {left}={right} := by\n    unfold '+' '.join(defs)+'\n    ring\n'
        text+=f'  rw [ha,hb,←mul_add,pole_comparison_reduced_{i},hc]\n\nend LeanVerification.PositiveDCompletion\n'
        (out/f'PoleComparison{i}.lean').write_text(re.sub(r'\^(\d+)',lambda m: '^('+m.group(1)+' : ℕ)',text))
    print('Emitted pole data and twelve coefficient identities')


if __name__=='__main__':main()
