#!/usr/bin/env python3
"""Independently check the bundled integer certificate data with sparse exact arithmetic.

This is a reproducibility diagnostic.  The proof authority is Lean's kernel,
which checks the corresponding identities and positivity lemmas independently.
"""
import argparse
import json
import math
import sys
from pathlib import Path

import sympy as s


def sparse(terms):
    return {tuple(m): int(c) for m, c in terms if c}


def expand_bernstein(terms, degrees):
    current = sparse(terms)
    for axis, degree in enumerate(degrees):
        result = {}
        for monomial, coefficient in current.items():
            for extra in range(degree - monomial[axis] + 1):
                key = list(monomial)
                key[axis] += extra
                key = tuple(key)
                value = coefficient * (-1) ** extra * math.comb(degree - monomial[axis], extra)
                result[key] = result.get(key, 0) + value
        current = {m: c for m, c in result.items() if c}
    return current


def check_bernstein(entries, label):
    count = 0
    for i, entry in enumerate(entries):
        terms = entry['bernstein']
        assert terms and all(c > 0 for _, c in terms), (label, i, 'strict coefficients')
        assert all(all(0 <= k <= d for k, d in zip(m, entry['degrees'])) for m, _ in terms)
        assert len(sparse(terms)) == len(terms), (label, i, 'duplicate indices')
        assert expand_bernstein(terms, entry['degrees']) == sparse(entry['atom']), (label, i, 'Bernstein identity')
        count += len(terms)
        print(f'{label} {i:02d}: {len(terms)} positive coefficients; exact Bernstein identity', flush=True)
    return count


def check_lower_cores(entries):
    a, t = s.symbols('a t')
    poly = lambda expression: s.Poly(expression, a, t, domain=s.ZZ)
    A, T, O, Z = poly(a), poly(t), poly(1), poly(0)
    F = O + (A - O) * T
    B = poly(2*a*a*t*t-a*a*t-4*a*t*t+6*a*t-a-5*t+5)
    C = poly(2+2*(a-1)*t+a*(a-1)*t*t)
    G = (F**3*C-A**3*T**2*B).exquo((O-T)**2)
    for index, entry in enumerate(entries):
        d = entry['rho_degree']
        maximum = max(d, max(m[0] for m, _ in entry['num']), max(m[1] for m, _ in entry['num']))
        fp, ap = [F**i for i in range(maximum+1)], [A**i for i in range(maximum+1)]
        evaluated = []
        for k in range(d+1):
            value = Z
            for (i, j, z), coefficient in entry['num']:
                if z == k:
                    value += int(coefficient)*ap[i]*fp[j]
            evaluated.append(value)
        pa, pt, p1 = [power for _, power in entry['factors']]
        for j, core in enumerate(entry['core_coefficients']):
            h = sum((math.comb(k,j)*evaluated[k]*ap[k-j]*fp[d-k] for k in range(j,d+1)), Z)
            powers = []
            for form in [A-O, T, O-T]:
                exponent = 0
                while True:
                    quotient, remainder = divmod(h, form)
                    if remainder:
                        break
                    h, exponent = quotient, exponent+1
                powers.append(exponent)
            assert powers == core['powers'], (index, j, 'core factor powers')
            assert {m: int(c) for m,c in h.terms()} == sparse(core['terms']), (index, j, 'core polynomial')
            ea, et, e1 = powers[0]-pa, 2*(d-j)+powers[1]-pt, 2*j+powers[2]-p1
            assert [ea,et,e1] == core['atom_powers'] and min(ea,et,e1) >= 0
            product = (A-O)**ea*A**(2*(d-j))*T**et*(O-T)**e1*B**(d-j)*G**j*h
            actual = {m: int(c)*2**m[0] for m,c in product.shift_list([1,0]).terms()}
            expected = {tuple(m[:2]):int(c) for m,c in entry['atom'] if m[2] == j}
            assert actual == expected, (index, j, 'lower atom')
        print(f'lower {index:02d}: all exact homogeneous coordinate cores', flush=True)


def check_source_and_poles(data, project):
    sys.path.insert(0, str(project / 'scripts/reflected_wedge'))
    from exact_data import load_certificates
    a,f,r = s.symbols('a f rho')
    P = lambda expression: s.Poly(expression,a,f,r,domain=s.ZZ)
    A,F,R,O,Z = P(a),P(f),P(r),P(1),P(0)
    ns = [P(c['num']) for c in load_certificates()[:10]]
    B=2*(F-A)*(O-F)*(O-R); H=(F-A)*(O-R); G=O-A*A*R; J=O+F
    C=A*R*(O-A*F); M=(O+A)*(F-A*R); base=G*J
    flow=(O+A)*R*(A*(O+A)*(F-A*R)*(O-F)+2*(O-A*F)*(F-A))
    tz=[B*J**3*G**3,-ns[0]*J**2*G,-ns[1]*J*G,-ns[2],-ns[3]]
    pole1=2*M*G*J**2+6*M*C*J+3*flow*J
    pole2=8*M*C*J+3*F*flow
    rz=ns[9]-A*(A+O)*H*J*G
    vz=[Z, ns[4]*G*J**3-A*J*H*M*B*G**3*J**3,
        2*ns[5]*G*J**2+A*J*H*M*ns[0]*G*J**2,
        ns[6]*J+A*J*H*M*ns[1]*G*J,
        2*ns[7]+A*J*H*M*ns[2], A*ns[8]+A*J*H*M*ns[3]]
    T=lambda i: tz[i] if 0<=i<len(tz) else Z
    V=lambda i: vz[i] if 0<=i<len(vz) else Z
    raw={key:[s.Poly.from_dict(sparse(terms),(a,f,r),domain=s.ZZ) for terms in data[key]] for key in ['phi','rx']}
    for i,q in enumerate(raw['phi']):
        assert q==(O+A)*T(i), ('phi source',i)
    for i,q in enumerate(raw['rx']):
        cs=A*H*J*(T(i)*base**2+2*T(i-1)*base*C+T(i-2)*C**2)
        cs+=rz*(J*base*T(i)+(J*C+F*base)*T(i-1)+F*C*T(i-2))
        cs+=A*H*(pole1*T(i-1)+pole2*T(i-2))+base*V(i)+C*V(i-1)
        assert H*q==(O+A)*cs, ('rx source',i)
    print('All twelve exact source coefficient identities', flush=True)
    poles={key:[P(s.sympify(expr)) for expr in data[key+'_pole']] for key in ['phi','rx']}
    for key in ['phi','rx']:
        d=len(raw[key])-1
        for j,q in enumerate(poles[key]):
            expected=sum((math.comb(i,j)*(-1)**i*base**(i-j)*C**(d-i)*raw[key][i] for i in range(j,d+1)),Z)
            assert q==expected, (key,'pole',j)
    for j,expression in enumerate(data['comparisons']):
        assert -poles['phi'][4]*poles['rx'][j+2]+poles['rx'][6]*poles['phi'][j]==P(s.sympify(expression)), ('comparison',j)
    print('All twelve exact pole coefficient identities and four comparisons', flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report',type=Path)
    args=parser.parse_args()
    source=Path(__file__).resolve().parent
    project=source.parents[1]
    upper=json.loads((source/'data/upper_certificates.json').read_text())
    lower=json.loads((source/'data/lower_certificates.json').read_text())
    data=json.loads((source/'data/source_coefficients.json').read_text())
    for i,(u,l) in enumerate(zip(upper,lower)):
        sign=-1 if i in (1,5) else 1
        assert sparse(l['num'])=={m:sign*c for m,c in sparse(u['num']).items()}, ('leaf equality',i)
    totals={'upper_positive_coefficients':check_bernstein(upper,'upper'),
            'lower_positive_coefficients':check_bernstein(lower,'lower')}
    check_lower_cores(lower)
    check_source_and_poles(data,project)
    totals.update({'source_identities':12,'pole_identities':12,'pole_comparisons':4,'status':'passed'})
    print(json.dumps(totals,indent=2),flush=True)
    if args.report:
        args.report.write_text(json.dumps(totals,indent=2)+'\n')


if __name__=='__main__':
    main()
