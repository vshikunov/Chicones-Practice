#!/usr/bin/env python3
"""Emit kernel-checkable upper positive-D polynomial certificates from exact data."""

import re
import argparse
import json
from pathlib import Path


def balanced(items, operator='+'):
    if not items:
        return '(0 : ℝ)' if operator == '+' else '(1 : ℝ)'
    if len(items) == 1:
        return items[0]
    middle = len(items) // 2
    return '(' + balanced(items[:middle], operator) + operator + balanced(items[middle:], operator) + ')'


def power(variable, exponent):
    return None if exponent == 0 else variable if exponent == 1 else f'({variable}^{exponent})'


def polynomial(terms, variables):
    return balanced([balanced([f'({coefficient} : ℝ)'] +
        [term for variable, exponent in zip(variables, monomial)
         if (term := power(variable, exponent))], '*') for monomial, coefficient in terms])


def expand_bernstein(terms, degrees, axes):
    from math import comb
    result = {}
    for monomial, coefficient in terms:
        active = {tuple(monomial[axis] for axis in axes): coefficient}
        for local, axis in enumerate(axes):
            transformed = {}
            for key, value in active.items():
                for extra in range(degrees[axis] - monomial[axis] + 1):
                    new_key = list(key)
                    new_key[local] += extra
                    new_key = tuple(new_key)
                    transformed[new_key] = transformed.get(new_key, 0) + value * (-1)**extra * comb(degrees[axis] - monomial[axis], extra)
            active = transformed
        for key, value in active.items():
            result[key] = result.get(key, 0) + value
    return [[list(key), value] for key, value in sorted(result.items(), reverse=True) if value]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    output = args.output or source
    output.mkdir(parents=True, exist_ok=True)
    entries = json.loads((source / 'data/upper_certificates.json').read_text())
    for index, entry in enumerate(entries):
        name = f'upperNum{index:02d}'
        atom = f'upperAtom{index:02d}'
        prefix = f'upperCertificate{index:02d}'
        degrees = entry['degrees']
        terms = entry['bernstein']
        header = '''noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 48000000
set_option maxRecDepth 50000

'''
        text = 'import LeanVerification.PositiveDCompletion.CertificateCoordinates\n\n' + header
        atom_coeff_names = []
        if index < 3:
            text += f'def {name} (a f rho : ℝ) : ℝ := {polynomial(entry["num"], ["a", "f", "rho"])}\n\n'
            text += f'def {atom} (a t z : ℝ) : ℝ := {polynomial(entry["atom"], ["a", "t", "z"])}\n\n'
            if entry['kind'] == 'ordinary':
                text += f'theorem {name}_map (a t z : ℝ) :\n    {name} a (a+(1-a)*t) z=(1-a)^{entry["factor_power"]}*{atom} a t z := by\n  unfold {name} {atom}\n  ring\n\n'
            else:
                corr = f'upperCorrelated{index:02d}'
                text += f'def {corr} (a f u : ℝ) : ℝ := {polynomial(entry["corr"], ["a", "f", "u"])}\n\n'
                text += f'theorem {name}_clear (a f rho : ℝ) :\n    f^{entry["rho_degree"]}*{name} a f rho={corr} a f (f*rho) := by\n  unfold {name} {corr}\n  ring\n\n'
                text += f'theorem {name}_map (a t z : ℝ) :\n    {corr} a (a+(1-a)*t) (a*z)=(1-a)^{entry["factor_power"]}*{atom} a t z := by\n  unfold {corr} {atom}\n  ring\n\n'
        else:
            dr = max(monomial[2] for monomial, _ in entry['num'])
            num_coeff_names = [f'{name}Coeff{j}' for j in range(dr+1)]
            atom_coeff_names = [f'{atom}Coeff{j}' for j in range(dr+1)]
            for j in range(dr+1):
                nt = [[monomial[:2], coefficient] for monomial, coefficient in entry['num'] if monomial[2] == j]
                at = [[monomial[:2], coefficient] for monomial, coefficient in entry['atom'] if monomial[2] == j]
                text += f'def {num_coeff_names[j]} (a f : ℝ) : ℝ := {polynomial(nt,["a","f"])}\n\n'
                text += f'def {atom_coeff_names[j]} (a t : ℝ) : ℝ := {polynomial(at,["a","t"])}\n\n'
            text += f'def {name} (a f rho : ℝ) : ℝ := '+balanced([f'({num_coeff_names[j]} a f)*rho^{j}' for j in range(dr+1)])+'\n\n'
            text += f'def {atom} (a t z : ℝ) : ℝ := '+balanced([f'({atom_coeff_names[j]} a t)*z^{j}' for j in range(dr+1)])+'\n\n'
            if entry['kind'] == 'correlated':
                corr = f'upperCorrelated{index:02d}'
                text += f'def {corr} (a f u : ℝ) : ℝ := '+balanced([f'({num_coeff_names[j]} a f)*f^{dr-j}*u^{j}' for j in range(dr+1)])+'\n\n'
                text += f'theorem {name}_clear (a f rho : ℝ) :\n    f^{dr}*{name} a f rho={corr} a f (f*rho) := by\n  unfold {name} {corr}\n  ring\n\n'
            for j in range(dr+1):
                left = f'{num_coeff_names[j]} a (a+(1-a)*t)'
                if entry['kind'] == 'correlated': left += f'*(a+(1-a)*t)^{dr-j}*a^{j}'
                text += f'theorem {name}Coeff{j}_map (a t : ℝ) :\n    {left}=(1-a)^{entry["factor_power"]}*{atom_coeff_names[j]} a t := by\n  unfold {num_coeff_names[j]} {atom_coeff_names[j]}\n  ring\n\n'
            if entry['kind'] == 'ordinary':
                text += f'theorem {name}_map (a t z : ℝ) :\n    {name} a (a+(1-a)*t) z=(1-a)^{entry["factor_power"]}*{atom} a t z := by\n  unfold {name} {atom}\n  rw ['+','.join(f'{name}Coeff{j}_map' for j in range(dr+1))+']\n  ring\n\n'
            else:
                text += f'theorem {name}_map (a t z : ℝ) :\n    {corr} a (a+(1-a)*t) (a*z)=(1-a)^{entry["factor_power"]}*{atom} a t z := by\n'
                for j in range(dr+1):
                    text += f'  have h{j} : {num_coeff_names[j]} a (a+(1-a)*t)*(a+(1-a)*t)^{dr-j}*(a*z)^{j}=(1-a)^{entry["factor_power"]}*{atom_coeff_names[j]} a t*z^{j} := by\n    rw [mul_pow,←mul_assoc,{name}Coeff{j}_map]\n'
                text += f'  unfold {corr} {atom}\n  rw ['+','.join(f'h{j}' for j in range(dr+1))+']\n  ring\n\n'
        text += 'end LeanVerification.PositiveDCompletion\n'
        (output / f'UpperPolynomial{index:02d}.lean').write_text(re.sub(r'\^(\d+)',lambda m: '^('+m.group(1)+' : ℕ)',text) if index>=8 else text)

        text = f'import LeanVerification.PositiveDCompletion.UpperPolynomial{index:02d}\n\n' + header
        groups = {}
        for monomial, coefficient in terms:
            groups.setdefault(monomial[0], []).append((monomial, coefficient))
        for ai, group in sorted(groups.items()):
            tgroups = {}
            for monomial, coefficient in group:
                tgroups.setdefault(monomial[1], []).append((monomial, coefficient))
            leaves = {}
            for tj, zterms in sorted(tgroups.items()):
                leaves[tj] = balanced([balanced([f'({coefficient} : ℝ)'] +
                    [term for term in [power('z', monomial[2]), power('(1-z)', degrees[2]-monomial[2])] if term], '*')
                    for monomial, coefficient in zterms])
            block = f'{prefix}Block{ai:02d}'
            body = balanced([balanced([term for term in [power('t', tj), power('(1-t)', degrees[1]-tj)] if term] + [leaves[tj]], '*')
                for tj in sorted(tgroups)])
            text += f'def {block} (t z : ℝ) : ℝ := {body}\n\n'
            expanded = polynomial(expand_bernstein(group, degrees, [1,2]), ['t','z'])
            text += f'theorem {block}_identity (t z : ℝ) :\n    {block} t z={expanded} := by\n'
            for tj in sorted(tgroups):
                text += f'  have hz{tj} : {leaves[tj]} = {polynomial(expand_bernstein(tgroups[tj], degrees, [2]), ["z"])} := by ring\n'
            text += f'  unfold {block}\n  simp only [' + ','.join(f'hz{tj}' for tj in sorted(tgroups)) + ']\n  ring\n\n'
            text += f'theorem {block}_pos {{t z : ℝ}} (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) :\n    0<{block} t z := by\n  have htc : 0<1-t := by linarith\n  have hzc : 0<1-z := by linarith\n  unfold {block}\n  positivity\n\n'
        certificate = balanced([balanced([term for term in [power('a', ai), power('(1-a)', degrees[0]-ai)] if term] + [f'({prefix}Block{ai:02d} t z)'], '*') for ai in sorted(groups)])
        text += f'def {prefix} (a t z : ℝ) : ℝ := {certificate}\n\n'
        text += f'theorem {prefix}_identity (a t z : ℝ) :\n    {atom} a t z={prefix} a t z := by\n  unfold {prefix}\n  rw [' + ','.join(f'{prefix}Block{ai:02d}_identity' for ai in sorted(groups)) + f']\n  unfold {atom} '+ ' '.join(atom_coeff_names)+'\n  ring\n\n'
        text += f'theorem {atom}_pos {{a t z : ℝ}} (ha : 0<a) (hau : a<1)\n    (ht : 0<t) (htu : t<1) (hz : 0<z) (hzu : z<1) : 0<{atom} a t z := by\n  rw [{prefix}_identity]\n  have hac : 0<1-a := by linarith\n'
        for ai in sorted(groups):
            text += f'  have hb{ai} := {prefix}Block{ai:02d}_pos ht htu hz hzu\n'
        text += f'  unfold {prefix}\n  positivity\n\n'
        extra = '\n    (hprod : f*rho<a)' if entry['kind'] == 'correlated' else ''
        text += f'theorem {name}_pos {{a f rho : ℝ}} (ha : 0<a) (hau : a<1)\n    (haf : a<f) (hf : f<1) (hr : 0<rho) (hru : rho<1){extra} : 0<{name} a f rho := by\n  obtain ⟨ht,htu,hfeq⟩ := upper_cube_coordinate hau haf hf\n  have hac : 0<1-a := by linarith\n'
        if entry['kind'] == 'ordinary':
            text += f'  have hp := {atom}_pos ha hau ht htu hr hru\n  have he := {name}_map a ((f-a)/(1-a)) rho\n  rw [hfeq] at he\n  rw [he]\n  exact mul_pos (pow_pos hac _) hp\n\n'
        else:
            text += f'  have hf0 : 0<f := ha.trans haf\n  obtain ⟨hu,huu,hueq⟩ := upper_correlated_coordinate ha hf0 hr hprod\n  have hp := {atom}_pos ha hau ht htu hu huu\n  have he := {name}_map a ((f-a)/(1-a)) (f*rho/a)\n  rw [hfeq,hueq,←{name}_clear] at he\n  have hpos : 0<f^{entry["rho_degree"]}*{name} a f rho := by rw [he];exact mul_pos (pow_pos hac _) hp\n  exact pos_of_mul_pos_right hpos (pow_pos hf0 _).le\n\n'
        text += 'end LeanVerification.PositiveDCompletion\n'
        (output / f'UpperCertificate{index:02d}.lean').write_text(re.sub(r'\^(\d+)',lambda m: '^('+m.group(1)+' : ℕ)',text) if index>=8 else text)
        print(f'{index:02d} {entry["name"]}: {len(terms)} exact positive coefficients')


if __name__ == '__main__':
    main()
