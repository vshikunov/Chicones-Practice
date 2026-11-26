#!/usr/bin/env python3
"""Emit exact source coefficient identities from bundled integer data."""
import re
import argparse
import json
from pathlib import Path
from generate_upper_certificates import balanced, polynomial


def call(name):
    return f'({name} a f rho)'


def summands(prefix, degree, var='w'):
    return balanced([f'{call(prefix+str(i))}*{var}^{i}' for i in range(degree+1)])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    root=Path(__file__).resolve().parent
    out=args.output or root
    out.mkdir(parents=True,exist_ok=True)
    data=json.loads((root/'data/source_coefficients.json').read_text())
    header='''noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 48000000
set_option maxRecDepth 50000

'''
    text='import LeanVerification.PositiveDCompletion.SourceNormalization\nimport LeanVerification.PositiveDCompletion.SourcePolynomialAlgebra\n\n'+header
    scalar_defs={
      'sourceBase':'modelG a rho*(1+f)',
      'sourceTCoeff0':'sourceB a f rho*(1+f)^3*(modelG a rho)^3',
      'sourceTCoeff1':'-weakNum00 a f rho*(1+f)^2*modelG a rho',
      'sourceTCoeff2':'-weakNum01 a f rho*(1+f)*modelG a rho',
      'sourceTCoeff3':'-weakNum02 a f rho',
      'sourceTCoeff4':'-weakNum03 a f rho',
      'sourcePoleCoeff1':'2*sourceM a f rho*modelG a rho*(1+f)^2+6*sourceM a f rho*sourceC a f rho*(1+f)+3*sourceFlow a f rho*(1+f)',
      'sourcePoleCoeff2':'8*sourceM a f rho*sourceC a f rho*(1+f)+3*f*sourceFlow a f rho',
      'sourceVCoeff0':'0',
      'sourceVCoeff1':'weakNum04 a f rho*modelG a rho*(1+f)^3-a*(1+f)*sourceH a f rho*sourceM a f rho*sourceB a f rho*(modelG a rho)^3*(1+f)^3',
      'sourceVCoeff2':'2*weakNum05 a f rho*modelG a rho*(1+f)^2+a*(1+f)*sourceH a f rho*sourceM a f rho*weakNum00 a f rho*modelG a rho*(1+f)^2',
      'sourceVCoeff3':'weakNum06 a f rho*(1+f)+a*(1+f)*sourceH a f rho*sourceM a f rho*weakNum01 a f rho*modelG a rho*(1+f)',
      'sourceVCoeff4':'2*weakNum07 a f rho+a*(1+f)*sourceH a f rho*sourceM a f rho*weakNum02 a f rho',
      'sourceVCoeff5':'a*weakNum08 a f rho+a*(1+f)*sourceH a f rho*sourceM a f rho*weakNum03 a f rho',
    }
    for name,expr in scalar_defs.items():
        text+=f'def {name} (a f rho : ℝ) : ℝ := {expr}\n\n'
    def T(i):return call('sourceTCoeff'+str(i)) if 0<=i<=4 else '(0 : ℝ)'
    def V(i):return call('sourceVCoeff'+str(i)) if 0<=i<=5 else '(0 : ℝ)'
    M=call('sourceBase');C=call('sourceC');H=call('sourceH');R=call('sourceRZero')
    for i in range(7):
        expr=f'a*{H}*(1+f)*({T(i)}*{M}^2+2*{T(i-1)}*{M}*{C}+{T(i-2)}*{C}^2)+{R}*((1+f)*{M}*{T(i)}+((1+f)*{C}+f*{M})*{T(i-1)}+f*{C}*{T(i-2)})+a*{H}*({call("sourcePoleCoeff1")}*{T(i-1)}+{call("sourcePoleCoeff2")}*{T(i-2)})+{M}*{V(i)}+{C}*{V(i-1)}'
        text+=f'def sourceRXCoeff{i} (a f rho : ℝ) : ℝ := {expr}\n\n'
    for key in ['phi','rx']:
        for i,terms in enumerate(data[key]):
            text+=f'def {key}NumCoeff{i} (a f rho : ℝ) : ℝ := {polynomial(terms,["a","f","rho"])}\n\n'
        text+=f'def {key}Numerator (a f rho w : ℝ) : ℝ := {summands(key+"NumCoeff",len(data[key])-1)}\n\n'
    text+=f'theorem sourceT_coefficients (a f rho w : ℝ) :\n    sourceT a f rho w={summands("sourceTCoeff",4)} := by\n  exact source_t_coeff_assembly (sourceB a f rho) (1+f) (modelG a rho)\n    (weakNum00 a f rho) (weakNum01 a f rho) (weakNum02 a f rho) (weakNum03 a f rho) w\n\n'
    text+=f'theorem sourceV_coefficients (a f rho w : ℝ) :\n    sourceV a f rho w={summands("sourceVCoeff",5)} := by\n  exact source_v_coeff_assembly a (sourceB a f rho) (1+f) (modelG a rho)\n    (sourceH a f rho) (sourceM a f rho)\n    '+ ' '.join(f'(weakNum{i:02d} a f rho)' for i in range(9))+' w\n\n'
    text+='theorem sourcePole_coefficients (a f rho w : ℝ) :\n    sourcePole a f rho w=sourcePoleCoeff1 a f rho*w+sourcePoleCoeff2 a f rho*w^2 := by rfl\n\n'
    text+='theorem transportN_source (a f rho w : ℝ) :\n    transportN a f rho w=sourceBase a f rho+sourceC a f rho*w := by rfl\n\n'
    text+=f'theorem sourceRXCleared_coefficients (a f rho w : ℝ) :\n    sourceRXCleared a f rho w={summands("sourceRXCoeff",6)} := by\n  unfold sourceRXCleared\n  rw [sourceT_coefficients,sourceV_coefficients,sourcePole_coefficients,transportN_source]\n'
    args=['sourceH','sourceBase','sourceC','sourceRZero','sourcePoleCoeff1','sourcePoleCoeff2']
    text+='  exact source_coeff_assembly a f '+ ' '.join(call(name) for name in args)+' w\n    '+ ' '.join(call('sourceTCoeff'+str(i)) for i in range(5))+'\n    '+ ' '.join(call('sourceVCoeff'+str(i)) for i in range(6))+'\n\n'
    text+='end LeanVerification.PositiveDCompletion\n'
    text=re.sub(r'\^(\d+)',lambda m: '^('+m.group(1)+' : ℕ)',text)
    split=text.index('theorem sourceT_coefficients')
    (out/'SourceCoefficientData.lean').write_text(text[:split]+'end LeanVerification.PositiveDCompletion\n')
    (out/'SourceCoefficientExpansion.lean').write_text('import LeanVerification.PositiveDCompletion.SourceCoefficientData\n\n'+header+text[split:])
    common=['sourceB','sourceH','sourceM','sourceC','sourceFlow','sourceBase','sourceRZero','modelG']+list(scalar_defs.keys())[1:]
    for key in ['phi','rx']:
      for i,terms in enumerate(data[key]):
        if key=='phi':lhs=f'phiNumCoeff{i} a f rho';rhs=f'(1+a)*sourceTCoeff{i} a f rho'
        else:lhs=f'sourceH a f rho*rxNumCoeff{i} a f rho';rhs=f'(1+a)*sourceRXCoeff{i} a f rho'
        unfold=[f'{key}NumCoeff{i}']+([] if key=='phi' else [f'sourceRXCoeff{i}'])+common+[f'weakNum{j:02d}' for j in range(10)]
        text='import LeanVerification.PositiveDCompletion.SourceCoefficientData\n\n'+header
        text+=f'theorem {key}_source_coefficient_{i} (a f rho : ℝ) :\n    {lhs}={rhs} := by\n  simp only ['+','.join(unfold)+']\n  ring\n\nend LeanVerification.PositiveDCompletion\n'
        (out/f'{key.title()}SourceCoefficient{i}.lean').write_text(re.sub(r'\^(\d+)',lambda m: '^('+m.group(1)+' : ℕ)',text))
    print('Emitted source data, five Phi and seven RX coefficient identities')


if __name__=='__main__':main()
