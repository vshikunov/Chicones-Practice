#!/usr/bin/env python3
"""Split the sextic pole identities into exact two-variable coefficient proofs."""
import argparse
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path

import sympy as sp

from generate_upper_certificates import balanced, polynomial


HEADER = '''noncomputable section
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 64000000
set_option maxRecDepth 60000

'''
END = 'end LeanVerification.PositiveDCompletion\n'


def pw(value, degree):
    return f'({value})^({degree} : ℕ)'


def value(coefficients, variable='rho'):
    return balanced([f'({c})*{pw(variable,k)}' for k,c in enumerate(coefficients)])


def symlean(expression):
    if expression.is_Integer:
        return f'({int(expression)} : ℝ)'
    if expression.is_Symbol:
        return str(expression)
    if expression.is_Add:
        return balanced([symlean(e) for e in expression.args])
    if expression.is_Mul:
        return balanced([symlean(e) for e in expression.args], '*')
    if expression.is_Pow:
        return pw(symlean(expression.base), int(expression.exp))
    raise ValueError(expression)


@dataclass
class Node:
    name: str
    degree: int
    expression: str
    coefficients: list
    children: tuple = ()
    operator: str = ''
    leaf_unfold: tuple = ()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--order',type=Path)
    args=parser.parse_args()
    root=Path(__file__).resolve().parent
    out=args.output or root
    out.mkdir(parents=True,exist_ok=True)
    source=json.loads((root/'data/source_coefficients.json').read_text())
    upper=json.loads((root/'data/upper_certificates.json').read_text())
    a,f,rho=sp.symbols('a f rho')
    nodes=[]; named={}; generic=set()

    def write(name,imports,body):
        text=''.join(f'import LeanVerification.PositiveDCompletion.{i}\n' for i in imports)+'\n'+HEADER+body+END
        if name == 'PoleRhoAlgebra':
            text = text.replace('open ReflectedWedgeCompletion\n', '')
        text=re.sub(r'\^(\d+)',lambda m:'^('+m.group(1)+' : ℕ)',text)
        (out/(name+'.lean')).write_text(text)

    def coefficients(node):
        return [f'{node.name}Coeff{k} a f' for k in range(node.degree+1)]

    def leaf(name,expression,cs,unfold=()):
        node=Node(name,len(cs)-1,expression,cs,leaf_unfold=unfold)
        nodes.append(node);named[name]=node
        return node

    def raw_leaf(name,expression,expr,unfold):
        poly=sp.Poly(expr,rho)
        cs=[]
        for k in range(poly.degree()+1):
            terms=[[list(m),int(c)] for m,c in sp.Poly(poly.nth(k),a,f,domain=sp.ZZ).terms() if c]
            cs.append(polynomial(terms,['a','f']))
        return leaf(name,expression,cs,unfold)

    def combine(left,right,operator):
        key=(left.name,right.name,operator)
        if key in named:return named[key]
        m,n=left.degree,right.degree
        generic.add((operator,m,n))
        lc,rc=coefficients(left),coefficients(right)
        if operator=='mul':
            cs=[balanced([f'({lc[i]})*({rc[k-i]})' for i in range(m+1) if 0<=k-i<=n]) for k in range(m+n+1)]
            expression=f'{left.name} a f rho*{right.name} a f rho'
        else:
            cs=[balanced(([lc[k]] if k<=m else [])+([rc[k]] if k<=n else [])) for k in range(max(m,n)+1)]
            expression=f'{left.name} a f rho+{right.name} a f rho'
        node=Node(f'poleRhoNode{len(nodes):03d}',len(cs)-1,expression,cs,(left,right),operator)
        nodes.append(node);named[key]=node
        return node

    one=leaf('poleRhoOne','1',['1'])

    def power(node,exponent):
        if exponent==0:return one
        if exponent==1:return node
        half=power(node,exponent//2)
        result=combine(half,half,'mul')
        return result if exponent%2==0 else combine(result,node,'mul')

    def product(ns):
        if len(ns)==1:return ns[0]
        middle=len(ns)//2
        return combine(product(ns[:middle]),product(ns[middle:]),'mul')

    def add(ns):
        if len(ns)==1:return ns[0]
        middle=len(ns)//2
        return combine(add(ns[:middle]),add(ns[middle:]),'add')

    R=leaf('poleRhoVariable','rho',['0','1'])
    B=leaf('poleRhoBase','sourceBase a f rho',['1+f','-a^2*(1+f)'],('sourceBase','modelG'))
    C=leaf('poleRhoC','sourceC a f rho',['0','a*(1-a*f)'],('sourceC',))
    G=leaf('poleRhoG','a^2*rho-1',['-1','a^2'])
    S=leaf('poleRhoS','a*rho-f',['-f','a'])
    RX=[]
    for i,terms in enumerate(source['rx']):
        expr=sp.Poly.from_dict({tuple(m):c for m,c in terms},(a,f,rho)).as_expr()
        RX.append(raw_leaf(f'poleRhoRaw{i}',f'rxNumCoeff{i} a f rho',expr,(f'rxNumCoeff{i}',)))
    UP={}
    for i in range(1,6):
        terms=upper[i]['num'];expr=sp.Poly.from_dict({tuple(m):c for m,c in terms},(a,f,rho)).as_expr()
        d=max(m[2] for m,c in terms)
        unfolds=(f'upperNum{i:02d}',)+tuple(f'upperNum{i:02d}Coeff{k}' for k in range(d+1) if i>=3)
        UP[i]=raw_leaf(f'poleRhoUpper{i}',f'upperNum{i:02d} a f rho',expr,unfolds)
    core00=2*f+a*f-3*a*f**2-3*rho*a**2+f*rho*a**2+2*f*rho*a**3
    p6=sp.sympify(source['rx_pole'][6])
    core04=sp.cancel(p6/(f*a**3*rho**3*(1+a)))
    K0=raw_leaf('poleRhoCore0','poleCore00 a f rho',core00,('poleCore00',))
    K4=raw_leaf('poleRhoCore4','poleCore04 a f rho',core04,('poleCore04',))
    lefts=[];rights=[]
    invariants=[3*a**2*(1+a)**6*(1+f)**5*(f-1),
                a**2*(1+a)**5*(1+f)**4*(f-1),
                a**2*(1+a)**4*(1+f)**3*(f-1),
                -2*a**2*(1+a)**3*(1+f)**2*(f-1),
                a**2*(1+a)**2*(1+f)*(f-1),a**2*(1+a),f*a**3*(1+a)]
    for j in range(7):
        invariant=leaf(f'poleRhoInvariant{j}',symlean(invariants[j]),[symlean(invariants[j])])
        factors=[invariant,power(R,3)]
        if j==0:factors += [power(G,3),power(S,4),power(K0,2)]
        elif j==1:factors += [power(G,2),power(S,3),UP[1]]
        elif j==2:factors += [G,power(S,2),UP[2]]
        elif j==3:factors += [G,S,UP[3]]
        elif j==4:factors += [G,UP[4]]
        elif j==5:factors += [UP[5]]
        else:factors += [K4]
        lefts.append(product(factors))
        terms=[]
        for i in range(j,7):
            scalar=leaf(f'poleRhoScalar{j}{i}',f'({math.comb(i,j)*(-1)**i} : ℝ)',[f'({math.comb(i,j)*(-1)**i} : ℝ)'])
            terms.append(product([scalar,power(B,i-j),power(C,6-i),RX[i]]))
        rights.append(add(terms))
        assert lefts[-1].degree==rights[-1].degree==12-j

    body=''
    for operator,m,n in sorted(generic):
        lc=[f'l{i}' for i in range(m+1)];rc=[f'r{i}' for i in range(n+1)]
        if operator=='mul':
            result=[balanced([f'{lc[i]}*{rc[k-i]}' for i in range(m+1) if 0<=k-i<=n]) for k in range(m+n+1)]
            left=f'({value(lc)})*({value(rc)})'
        else:
            result=[balanced(([lc[k]] if k<=m else [])+([rc[k]] if k<=n else [])) for k in range(max(m,n)+1)]
            left=f'({value(lc)})+({value(rc)})'
        body+=f'theorem pole_rho_{operator}_{m}_{n} (rho '+ ' '.join(lc+rc)+f' : ℝ) :\n    {left}={value(result)} := by ring\n\n'
    write('PoleRhoAlgebra',['PolePolynomialAlgebra'],body)
    body=''
    for node in nodes:
        body+=f'def {node.name} (a f rho : ℝ) : ℝ := {node.expression}\n\n'
        for k,coefficient in enumerate(node.coefficients):
            body+=f'def {node.name}Coeff{k} (a f : ℝ) : ℝ := {coefficient}\n\n'
    write('PoleRhoData',['PoleCoefficientData','PoleRhoAlgebra'],body)
    # Every node proof sees only its immediate coefficient functions.  No
    # three-variable expanded source polynomial enters a product normalization.
    body=''
    for node in nodes:
        cs=coefficients(node)
        body+=f'theorem {node.name}_eval (a f rho : ℝ) :\n    {node.name} a f rho={value(cs)} := by\n'
        if node.children:
            left,right=node.children
            body+=f'  unfold {node.name}\n  rw [{left.name}_eval'
            if left.name!=right.name:body+=f',{right.name}_eval'
            body+=']\n'
            arguments=' '.join(f'({c})' for c in coefficients(left)+coefficients(right))
            body+='  simpa only ['+','.join(f'{node.name}Coeff{k}' for k in range(node.degree+1))+'] using\n'
            body+=f'    pole_rho_{node.operator}_{left.degree}_{right.degree} rho {arguments}\n\n'
        else:
            body+='  unfold '+' '.join([node.name]+[f'{node.name}Coeff{k}' for k in range(node.degree+1)]+list(node.leaf_unfold))+'\n  ring\n\n'
    write('PoleRhoExpansion',['PoleRhoData'],body)
    order=['PoleRhoAlgebra','PoleRhoData','PoleRhoExpansion']

    def reachable(node):
        found={node.name}
        for child in node.children:found.update(reachable(child))
        return found

    for j,(left,right) in enumerate(zip(lefts,rights)):
        reachable_names=reachable(left)|reachable(right)
        coeffdefs=[f'{node.name}Coeff{k}' for node in nodes if node.name in reachable_names for k in range(node.degree+1)]
        parts=[]
        for k in range(left.degree+1):
            name=f'RxPoleRho{j}Coefficient{k:02d}'
            text=f'theorem rx_pole_rho_{j}_{k} (a f : ℝ) :\n    {left.name}Coeff{k} a f={right.name}Coeff{k} a f := by\n'
            text+='  simp only ['+','.join(coeffdefs)+']\n  ring\n\n'
            write(name,['PoleRhoData'],text)
            parts.append(name);order.append(name)
        original=(out/f'RxPoleCoefficient{j}.lean').read_text()
        statement=original[original.index(f'theorem rx_pole_coefficient_{j}'):original.index(' := by',original.index(f'theorem rx_pole_coefficient_{j}'))]
        text=statement+' := by\n'
        left_unfold=[n.name for n in nodes if n.name in reachable(left)]
        right_unfold=[n.name for n in nodes if n.name in reachable(right)]
        text+=f'  have hl : rxPoleCoeff{j} a f rho={left.name} a f rho := by\n'
        text+='    simp only ['+','.join([f'rxPoleCoeff{j}']+left_unfold)+']\n    ring\n'
        text+=f'  have hr : {right.name} a f rho='+statement.split('=')[1].strip()+' := by\n'
        text+='    simp only ['+','.join(right_unfold)+']\n    ring\n'
        text+=f'  rw [hl,←hr,{left.name}_eval,{right.name}_eval]\n'
        text+='  rw ['+','.join(f'rx_pole_rho_{j}_{k}' for k in range(left.degree+1))+']\n\n'
        write(f'RxPoleCoefficient{j}',['PoleRhoExpansion']+parts,text)
        order.append(f'RxPoleCoefficient{j}')
    if args.order:args.order.write_text(json.dumps(order,indent=2)+'\n')
    print(f'Emitted {len(nodes)} shared polynomial nodes, {len(generic)} generic identities and70 coefficient checks')


if __name__=='__main__':
    main()
