#!/usr/bin/env python3
"""Emit exact Bernstein certificates, split by powers of the third variable."""
import re
import argparse
import json
import math
from pathlib import Path
from generate_upper_certificates import balanced, power, polynomial, expand_bernstein


def sum_powers(names, args, variable):
    return balanced([f'({name} {args})*{variable}^{j}' for j,name in enumerate(names)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    output = args.output or source
    output.mkdir(parents=True, exist_ok=True)
    entries = json.loads((source/'data/lower_certificates.json').read_text())
    for index, entry in enumerate(entries):
        name=f'lowerNum{index:02d}';atom=f'lowerAtom{index:02d}';prefix=f'lowerCertificate{index:02d}'
        degrees=entry['degrees'];terms=entry['bernstein'];du=degrees[2]
        assert all(coefficient>0 for _,coefficient in terms)
        header='''noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

'''
        atom_names=[f'{atom}Coeff{k}' for k in range(du+1)]
        dr=entry['rho_degree']
        raw_names=[f'{name}Coeff{k}' for k in range(dr+1)]
        core_names=[f'lowerCore{index:02d}Coeff{k}' for k in range(dr+1)]
        text='import LeanVerification.PositiveDCompletion.LowerCoordinates\n\n'+header
        for k,rname in enumerate(raw_names):
            rt=[[monomial[:2],coefficient] for monomial,coefficient in entry['num'] if monomial[2]==k]
            text+=f'def {rname} (a f : ℝ) : ℝ := {polynomial(rt,["a","f"])}\n\n'
        text+=f'def {name} (a f rho : ℝ) : ℝ := {sum_powers(raw_names,"a f","rho")}\n\n'
        for k,cname in enumerate(core_names):
            text+=f'def {cname} (a t : ℝ) : ℝ := {polynomial(entry["core_coefficients"][k]["terms"],["a","t"])}\n\n'
        for k,aname in enumerate(atom_names):
            ea,et,e1=entry['core_coefficients'][k]['atom_powers']
            body=f'(2*x)^{ea}*(1+2*x)^{2*(dr-k)}*t^{et}*(1-t)^{e1}*(lowerCubeB (1+2*x) t)^{dr-k}*(lowerCubeG (1+2*x) t)^{k}*{core_names[k]} (1+2*x) t'
            text+=f'def {aname} (x t : ℝ) : ℝ := {body}\n\n'
        text+=f'def {atom} (x t u : ℝ) : ℝ := {sum_powers(atom_names,"x t","u")}\n\n'
        for k,cname in enumerate(core_names):
            ea,et,e1=entry['core_coefficients'][k]['powers']
            expr=balanced([f'({math.comb(i,k)} : ℝ)*{raw_names[i]} a (lowerCubeF a t)*a^{i-k}*(lowerCubeF a t)^{dr-i}' for i in range(k,dr+1)])
            text+=f'theorem {cname}_map (a t : ℝ) :\n    {expr}=(a-1)^{ea}*t^{et}*(1-t)^{e1}*{cname} a t := by\n  unfold lowerCubeF {cname} '+' '.join(raw_names[k:])+'\n  ring\n\n'
        text+='end LeanVerification.PositiveDCompletion\n'
        (output/f'LowerPolynomial{index:02d}.lean').write_text(re.sub(r'\^(\d+)',lambda m: '^('+m.group(1)+' : ℕ)',text))
        text=f'import LeanVerification.PositiveDCompletion.LowerPolynomial{index:02d}\n\n'+header
        groups={}
        for monomial,coefficient in terms:groups.setdefault(monomial[0],[]).append((monomial,coefficient))
        block_coeffs={};weights={}
        for xi,group in sorted(groups.items()):
            weight=f'{prefix}Weight{xi:02d}';weights[xi]=weight
            text+=f'def {weight} (x : ℝ) : ℝ := x^{xi}*(1-x)^{degrees[0]-xi}\n\n'
            text+=f'theorem {weight}_pos {{x : ℝ}} (hx : 0<x) (hxu : x<1) : 0<{weight} x := by\n  have hc : 0<1-x := by linarith\n  unfold {weight}\n  positivity\n\n'
            tgroups={}
            for monomial,coefficient in group:tgroups.setdefault(monomial[1],[]).append((monomial,coefficient))
            leaves={}
            for tj,uterms in sorted(tgroups.items()):
                leaves[tj]=balanced([balanced([f'({coefficient} : ℝ)']+[term for term in [power('u',monomial[2]),power('(1-u)',du-monomial[2])] if term],'*') for monomial,coefficient in uterms])
            block=f'{prefix}Block{xi:02d}'
            body=balanced([balanced([term for term in [power('t',tj),power('(1-t)',degrees[1]-tj)] if term]+[leaves[tj]],'*') for tj in sorted(tgroups)])
            text+=f'def {block} (t u : ℝ) : ℝ := {body}\n\n'
            expanded=expand_bernstein(group,degrees,[1,2])
            bnames=[f'{block}Coeff{k}' for k in range(du+1)];block_coeffs[xi]=bnames
            for k,bname in enumerate(bnames):
                bt=[[[monomial[0]],coefficient] for monomial,coefficient in expanded if monomial[1]==k]
                text+=f'def {bname} (t : ℝ) : ℝ := {polynomial(bt,["t"])}\n\n'
            text+=f'theorem {block}_identity (t u : ℝ) :\n    {block} t u={sum_powers(bnames,"t","u")} := by\n'
            for tj in sorted(tgroups):text+=f'  have hu{tj} : {leaves[tj]}={polynomial(expand_bernstein(tgroups[tj],degrees,[2]),["u"])} := by ring\n'
            text+=f'  unfold {block}\n  try simp only ['+','.join(f'hu{tj}' for tj in sorted(tgroups))+']\n  unfold '+' '.join(bnames)+'\n  ring\n\n'
            text+=f'theorem {block}_pos {{t u : ℝ}} (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :\n    0<{block} t u := by\n  have htc : 0<1-t := by linarith\n  have huc : 0<1-u := by linarith\n  unfold {block}\n  positivity\n\n'
        for k,aname in enumerate(atom_names):
            rhs=balanced([f'({weights[xi]} x)*({block_coeffs[xi][k]} t)' for xi in sorted(groups)])
            text+=f'theorem {aname}_identity (x t : ℝ) :\n    {aname} x t={rhs} := by\n  unfold {aname} {core_names[k]} lowerCubeB lowerCubeG '+' '.join(weights[xi] for xi in sorted(groups))+' '+' '.join(block_coeffs[xi][k] for xi in sorted(groups))+'\n  ring\n\n'
        certificate=balanced([f'({weights[xi]} x)*({prefix}Block{xi:02d} t u)' for xi in sorted(groups)])
        text+=f'def {prefix} (x t u : ℝ) : ℝ := {certificate}\n\n'
        text+=f'theorem {prefix}_identity (x t u : ℝ) :\n    {atom} x t u={prefix} x t u := by\n  unfold {prefix} {atom}\n  rw ['+','.join([f'{prefix}Block{xi:02d}_identity' for xi in sorted(groups)]+[f'{aname}_identity' for aname in atom_names])+']\n  ring\n\n'
        text+=f'theorem {atom}_pos {{x t u : ℝ}} (hx : 0<x) (hxu : x<1) (ht : 0<t) (htu : t<1) (hu : 0<u) (huu : u<1) :\n    0<{atom} x t u := by\n  rw [{prefix}_identity]\n'
        for xi in sorted(groups):
            text+=f'  have hb{xi} := {prefix}Block{xi:02d}_pos ht htu hu huu\n'
            text+=f'  have hw{xi} := {weights[xi]}_pos hx hxu\n'
        text+=f'  unfold {prefix}\n  positivity\n\nend LeanVerification.PositiveDCompletion\n'
        (output/f'LowerCertificate{index:02d}.lean').write_text(re.sub(r'\^(\d+)',lambda m: '^('+m.group(1)+' : ℕ)',text))
        print(f'{index:02d} {entry["name"]}: {len(terms)} positive coefficients, {du+1} final coefficient checks')


if __name__ == '__main__':
    main()
