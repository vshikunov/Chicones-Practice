#!/usr/bin/env python3
"""Emit upper07/08/09 Bernstein proofs with separate third-variable coefficients.

The exact Bernstein input is unchanged. The original upperNumNN_pos theorem
and application are retained, including the ordinary (07) or correlated
(08/09) parameter premises. Only the auxiliary certificate representation
and its proof decomposition change.
"""
import argparse,json,re
from pathlib import Path
from generate_upper_certificates import balanced,power,polynomial,expand_bernstein
from partition_certificates import decls


def sum_powers(names,args,var):return balanced([f'({name} {args})*{var}^{j}' for j,name in enumerate(names)])


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path)
    p.add_argument('--indices',type=int,nargs='+',default=[7,8,9],choices=range(3,10),
                   help='Coefficient-separated certificate indices (default: 7 8 9).')
    args=p.parse_args();root=Path(__file__).resolve().parent;out=args.output or root
    if len(set(args.indices)) != len(args.indices):p.error('--indices must not contain duplicates')
    out.mkdir(parents=True,exist_ok=True)
    data=json.loads((root/'data/upper_certificates.json').read_text())
    header='''noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

'''
    for i in args.indices:
        e=data[i];degrees=e['degrees'];dz=degrees[2];atom=f'upperAtom{i:02d}';pre=f'upperCertificate{i:02d}'
        original=(out/f'UpperCertificate{i:02d}.lean').read_text()
        application=next(v for k,n,v in decls(original) if n==f'upperNum{i:02d}_pos')
        text=f'import LeanVerification.PositiveDCompletion.UpperPolynomial{i:02d}\n\n'+header
        groups={}
        for m,c in e['bernstein']:groups.setdefault(m[0],[]).append((m,c))
        coeffnames={};weights={}
        for ai,terms in sorted(groups.items()):
            weight=f'{pre}Weight{ai:02d}';weights[ai]=weight
            text+=f'def {weight} (a : ℝ) : ℝ := a^{ai}*(1-a)^{degrees[0]-ai}\n\n'
            text+=f'theorem {weight}_pos {{a : ℝ}} (ha : 0<a) (hau : a<1) : 0<{weight} a := by\n  have hac : 0<1-a := by linarith\n  unfold {weight}\n  positivity\n\n'
            tgroups={}
            for m,c in terms:tgroups.setdefault(m[1],[]).append((m,c))
            leaves={j:balanced([balanced([f'({c} : ℝ)']+[q for q in [power('z',m[2]),power('(1-z)',dz-m[2])] if q],'*') for m,c in vals]) for j,vals in tgroups.items()}
            block=f'{pre}Block{ai:02d}'
            body=balanced([balanced([q for q in [power('t',j),power('(1-t)',degrees[1]-j)] if q]+[leaves[j]],'*') for j in sorted(tgroups)])
            text+=f'def {block} (t z : ℝ) : ℝ := {body}\n\n'
            expanded=expand_bernstein(terms,degrees,[1,2]);names=[f'{block}Coeff{k}' for k in range(dz+1)];coeffnames[ai]=names
            for k,name in enumerate(names):
                tt=[[[m[0]],c] for m,c in expanded if m[1]==k]
                text+=f'def {name} (t : ℝ) : ℝ := {polynomial(tt,["t"])}\n\n'
            text+=f'theorem {block}_identity (t z : ℝ) :\n    {block} t z={sum_powers(names,"t","z")} := by\n'
            for j in sorted(tgroups):text+=f'  have hz{j} : {leaves[j]}={polynomial(expand_bernstein(tgroups[j],degrees,[2]),["z"])} := by ring\n'
            text+=f'  unfold {block}\n  simp only ['+','.join(f'hz{j}' for j in sorted(tgroups))+']\n  unfold '+' '.join(names)+'\n  ring\n\n'
            text+=f'theorem {block}_pos {{t z : ℝ}} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :\n    0<{block} t z := by\n  have htc : 0<1-t := by linarith\n  have hzc : 0<1-z := by linarith\n  unfold {block}\n  positivity\n\n'
        for k in range(dz+1):
            aname=f'{atom}Coeff{k}';rhs=balanced([f'({weights[ai]} a)*({coeffnames[ai][k]} t)' for ai in sorted(groups)])
            text+=f'theorem {aname}_identity (a t : ℝ) :\n    {aname} a t={rhs} := by\n  unfold {aname} '+' '.join(weights.values())+' '+' '.join(coeffnames[ai][k] for ai in sorted(groups))+'\n  ring\n\n'
        certificate=balanced([f'({weights[ai]} a)*({pre}Block{ai:02d} t z)' for ai in sorted(groups)])
        text+=f'def {pre} (a t z : ℝ) : ℝ := {certificate}\n\n'
        text+=f'theorem {pre}_identity (a t z : ℝ) :\n    {atom} a t z={pre} a t z := by\n  unfold {pre} {atom}\n  rw ['+','.join([f'{pre}Block{ai:02d}_identity' for ai in sorted(groups)]+[f'{atom}Coeff{k}_identity' for k in range(dz+1)])+']\n  ring\n\n'
        text+=f'theorem {atom}_pos {{a t z : ℝ}} (ha : 0<a) (hau : a<1)\n    (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) : 0<{atom} a t z := by\n  rw [{pre}_identity]\n'
        for ai in sorted(groups):text+=f'  have hb{ai} := {pre}Block{ai:02d}_pos ht htu hz hzu\n  have hw{ai} := {weights[ai]}_pos ha hau\n'
        text+=f'  unfold {pre}\n  positivity\n\n'
        text=re.sub(r'\^(\d+)',lambda m:'^('+m.group(1)+' : ℕ)',text)
        text+=application+'end LeanVerification.PositiveDCompletion\n'
        (out/f'UpperCertificate{i:02d}.lean').write_text(text)
    print('Emitted coefficient-separated certificates: '+', '.join(f'upper{i:02d}' for i in args.indices))


if __name__=='__main__':main()
