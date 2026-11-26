#!/usr/bin/env python3
"""Replace generated two-variable ring identities with kernel coefficient checks.

The generated theorem statements are unchanged.  An expression interpreter
proves normalization soundness; each finite integer calculation is checked by
Lean's ordinary kernel. This emitter neither invokes nor trusts native evaluation.
"""
import argparse
import json
import re
from pathlib import Path


def constant(n):
    return ('coeff', int(n))


class Definitions:
    def __init__(self, directory, fallback=None):
        self.definitions = {}
        self.used = set()
        self.cache = {}
        pattern = re.compile(r'^def (\w+) \(([\w\s]+) : ℝ\) : ℝ :=\s*(.*?)(?=^(?:def|theorem|end|namespace)\b|\Z)', re.M | re.S)
        directories = list(dict.fromkeys(([fallback] if fallback else []) + [directory]))
        for source in directories:
            for path in source.glob('*.lean'):
                for name, parameters, body in pattern.findall(path.read_text()):
                    self.definitions[name] = (parameters.split(), body.strip())

    def expression(self, text, variables):
        return Parser(self, text, variables).parse()

    def apply(self, name, arguments):
        self.used.add(name)
        key = (name, tuple(arguments))
        if key not in self.cache:
            parameters, body = self.definitions[name]
            self.cache[key] = self.expression(body, dict(zip(parameters, arguments)))
        return self.cache[key]


class Parser:
    def __init__(self, definitions, text, variables):
        self.definitions = definitions
        self.variables = variables
        text = re.sub(r':\s*[ℝℕℤ]', '', text)
        self.tokens = re.findall(r'\d+|\w+|[()+*^\-]', text)
        residue = re.sub(r'\d+|\w+|[()+*^\-]|\s+', '', text)
        if residue:
            raise ValueError(f'Unsupported polynomial syntax: {residue!r}')
        self.position = 0

    def peek(self):
        return self.tokens[self.position] if self.position < len(self.tokens) else None

    def take(self):
        token = self.peek()
        if token is None:
            raise ValueError('Unexpected end of polynomial')
        self.position += 1
        return token

    def atom(self):
        token = self.take()
        if token == '(':
            result = self.expression(0)
            if self.take() != ')':
                raise ValueError('Unbalanced polynomial parentheses')
            return result
        if token == '-':
            return ('neg', self.expression(30))
        if token.isdigit():
            return constant(token)
        if token in self.variables:
            return self.variables[token]
        if token in self.definitions.definitions:
            parameters, _ = self.definitions.definitions[token]
            arguments = [self.atom() for _ in parameters]
            return self.definitions.apply(token, arguments)
        raise ValueError(f'Unknown polynomial identifier {token}')

    def expression(self, precedence):
        result = self.atom()
        levels = {'+':10, '-':10, '*':20, '^':40}
        while self.peek() in levels and levels[self.peek()] >= precedence:
            operator = self.take()
            right = self.expression(levels[operator] + (0 if operator == '^' else 1))
            if operator == '^':
                if right[0] != 'coeff' or right[1] < 0:
                    raise ValueError('Polynomial exponent is not a natural literal')
                result = ('pow', result, right[1])
            elif operator == '*':
                result = ('times', result, right)
            elif operator == '+':
                result = ('plus', result, right)
            else:
                result = ('plus', result, ('neg', right))
        return result

    def parse(self):
        result = self.expression(0)
        if self.position != len(self.tokens):
            raise ValueError(f'Unused polynomial tokens {self.tokens[self.position:self.position+10]}')
        return result


def lean(expression):
    kind = expression[0]
    if kind in ('x', 't'):
        return '.' + kind
    if kind == 'coeff':
        return f'(.coeff {expression[1]})'
    if kind == 'neg':
        return f'(.neg {lean(expression[1])})'
    if kind == 'pow':
        return f'(.pow {lean(expression[1])} {expression[2]})'
    return f'(.{kind} {lean(expression[1])} {lean(expression[2])})'


def dag_certificate(lhs, rhs, prefix, node_budget=0):
    """Check each integer arithmetic node against its literal normal form."""
    nodes, indices, normal_forms, costs = [], {}, {}, {}
    forced = {lhs, rhs}

    def visit(node):
        if node in costs:
            return costs[node]
        kind = node[0]
        cost = 1
        if kind in ('neg', 'pow'):
            cost += visit(node[1])
        elif kind in ('plus', 'times'):
            cost += visit(node[1]) + visit(node[2])
        if kind == 'pow' and node[2] > 0:
            visit(('pow', node[1], node[2] - 1))
        if node_budget == 0 or kind == 'pow' or node in forced or cost > node_budget:
            indices[node] = len(nodes)
            nodes.append(node)
            cost = 1
        costs[node] = cost
        return cost

    visit(lhs)
    visit(rhs)

    def normal(node):
        if node in normal_forms:
            return normal_forms[node]
        kind = node[0]
        if kind == 'coeff':
            result = {(0, 0): node[1]} if node[1] else {}
        elif kind == 'x':
            result = {(1, 0): 1}
        elif kind == 't':
            result = {(0, 1): 1}
        elif kind == 'neg':
            result = {m: -c for m, c in normal(node[1]).items()}
        elif kind == 'plus':
            result = normal(node[1]).copy()
            for monomial, coefficient in normal(node[2]).items():
                result[monomial] = result.get(monomial, 0) + coefficient
        else:
            if kind == 'pow':
                if node[2] == 0:
                    result = {(0, 0): 1}
                    normal_forms[node] = result
                    return result
                left, right = normal(('pow', node[1], node[2] - 1)), normal(node[1])
            else:
                left, right = normal(node[1]), normal(node[2])
            result = {}
            for (i, j), c in left.items():
                for (k, l), d in right.items():
                    key = (i + k, j + l)
                    result[key] = result.get(key, 0) + c * d
        result = {m: c for m, c in result.items() if c}
        normal_forms[node] = result
        return result

    def matrix(poly):
        if not poly:
            return '[]'
        rows = []
        for i in range(max(m[0] for m in poly) + 1):
            row = {j: c for (k, j), c in poly.items() if k == i}
            rows.append('[' + ','.join(str(row.get(j, 0)) for j in range(max(row, default=-1) + 1)) + ']')
        return '[' + ','.join(rows) + ']'

    def ename(node):
        return f'{prefix}_node{indices[node]:04d}'

    def nname(node):
        return f'{prefix}_normal{indices[node]:04d}'

    def theorem(node):
        return f'{prefix}_step{indices[node]:04d}'

    def syntax(node, expand=False):
        if node in indices and not expand:
            return ename(node)
        kind = node[0]
        if kind in ('x', 't'):
            return '.' + kind
        if kind == 'coeff':
            return f'(.coeff {node[1]})'
        if kind == 'neg':
            return f'(.neg {syntax(node[1])})'
        if kind == 'pow':
            return f'(.pow {syntax(node[1])} {node[2]})'
        return f'(.{kind} {syntax(node[1])} {syntax(node[2])})'

    def boundaries(node, expand=False):
        if node in indices and not expand:
            return [node]
        kind = node[0]
        if kind in ('neg', 'pow'):
            return boundaries(node[1])
        if kind in ('plus', 'times'):
            return list(dict.fromkeys(boundaries(node[1]) + boundaries(node[2])))
        return []

    output = []
    qualified = 'CertificateKernel.DensePolynomial.'
    for node in nodes:
        kind = node[0]
        expression = syntax(node, expand=True)
        output.append(f'private noncomputable def {ename(node)} : {qualified}Expr := {expression}\n\n')
        output.append(f'private noncomputable def {nname(node)} : {qualified}Bi := {matrix(normal(node))}\n\n')
        output.append(f'private theorem {theorem(node)} : {ename(node)}.normal={nname(node)} := by\n')
        if kind == 'pow' and node[2] > 0:
            previous = ('pow', node[1], node[2] - 1)
            output.append(f'  change {qualified}canonical ({qualified}bmul {ename(previous)}.normal ({qualified}Expr.normal {syntax(node[1])}))={nname(node)}\n')
            children = list(dict.fromkeys([previous] + boundaries(node[1])))
        else:
            output.append(f'  change {qualified}Expr.normal {expression}={nname(node)}\n')
            children = boundaries(node, expand=True)
        simp_terms = [theorem(child) for child in children] + [qualified + 'Expr.normal']
        output.append('  simp only [' + ','.join(simp_terms) + ']\n')
        output.append('  all_goals rfl\n\n')
    assert normal(lhs) == normal(rhs), 'Generated integer normal forms differ'
    output.append(f'private theorem {prefix}_checked :\n    decide ({ename(lhs)}.normal={ename(rhs)}.normal)=true := by\n')
    root_steps = list(dict.fromkeys([theorem(lhs), theorem(rhs)]))
    output.append('  rw [' + ','.join(root_steps) + ']\n  rfl\n\n')
    return ''.join(output), ename(lhs), ename(rhs), [ename(node) for node in nodes]


def cached_tree_certificate(lhs, rhs, prefix, local_checks=False, validity=False, sparse=False):
    """Emit shared certificate data and a single kernel-checked Boolean guard."""
    nodes, indices, normals = [], {}, {}

    def visit(node):
        if node in indices:
            return
        if node[0] in ('neg', 'pow'):
            visit(node[1])
        elif node[0] in ('plus', 'times'):
            visit(node[1])
            visit(node[2])
        if validity and node[0]=='pow' and node[2]>0:
            visit(('pow',node[1],node[2]-1))
        indices[node] = len(nodes)
        nodes.append(node)

    visit(lhs)
    visit(rhs)

    def multiply(left, right):
        result = {}
        for (i, j), c in left.items():
            for (k, l), d in right.items():
                key = (i+k, j+l)
                result[key] = result.get(key, 0) + c*d
        return {m:c for m,c in result.items() if c}

    def normal(node):
        if node in normals:
            return normals[node]
        kind = node[0]
        if kind == 'coeff':
            result = {(0,0):node[1]} if node[1] else {}
        elif kind == 'x':
            result = {(1,0):1}
        elif kind == 't':
            result = {(0,1):1}
        elif kind == 'neg':
            result = {m:-c for m,c in normal(node[1]).items()}
        elif kind == 'plus':
            result = normal(node[1]).copy()
            for m,c in normal(node[2]).items():
                result[m] = result.get(m,0)+c
            result = {m:c for m,c in result.items() if c}
        elif kind == 'times':
            result = multiply(normal(node[1]),normal(node[2]))
        else:
            result = {(0,0):1}
            for _ in range(node[2]):
                result = multiply(result,normal(node[1]))
        normals[node] = result
        return result

    def matrix(poly):
        if sparse:
            return '['+','.join(f'(({i},{j}),{c})' for (i,j),c in sorted(poly.items()))+']'
        if not poly:
            return '[]'
        rows=[]
        for i in range(max(m[0] for m in poly)+1):
            row={j:c for (k,j),c in poly.items() if k==i}
            rows.append('['+','.join(str(row.get(j,0)) for j in range(max(row,default=-1)+1))+']')
        return '['+','.join(rows)+']'

    def name(node):
        return f'{prefix}_cert{indices[node]:04d}'

    output=[]
    qualified='CertificateKernel.'+('SparsePolynomial' if sparse else 'PolynomialDAG')+'.'
    for node in nodes:
        kind=node[0]
        cache=matrix(normal(node))
        if kind=='coeff':
            expression=f'.coeff {cache} {node[1]}'
        elif kind in ('x','t'):
            expression=f'.{kind} {cache}'
        elif kind=='neg':
            expression=f'.neg {cache} {name(node[1])}'
        elif kind=='pow':
            expression=f'.pow {cache} {name(node[1])} {node[2]}'
        else:
            expression=f'.{kind} {cache} {name(node[1])} {name(node[2])}'
        output.append(f'private noncomputable def {name(node)} : {qualified}Cert := {expression}\n\n')
        if validity:
            output.append(f'private theorem {name(node)}_valid : {qualified}Valid {name(node)} := by\n')
            if kind=='coeff':
                output.append(f'  exact {qualified}Valid.coeff {name(node)}.normal {node[1]} (Eq.refl true)\n\n')
            elif kind in ('x','t'):
                output.append(f'  exact {qualified}Valid.{kind} {name(node)}.normal (Eq.refl true)\n\n')
            elif kind in ('plus','times'):
                output.append(f'  exact {qualified}Valid.{kind} {name(node)}.normal {name(node[1])} {name(node[2])}\n')
                output.append(f'    {name(node[1])}_valid {name(node[2])}_valid (Eq.refl true)\n\n')
            elif kind=='neg':
                output.append(f'  exact {qualified}Valid.neg {name(node)}.normal {name(node[1])} {name(node[1])}_valid (Eq.refl true)\n\n')
            elif node[2]>0:
                previous=('pow',node[1],node[2]-1)
                output.append(f'  exact {qualified}Valid.pow_succ {name(node)}.normal {name(previous)}.normal {name(node[1])} {node[2]-1}\n')
                output.append(f'    {name(node[1])}_valid {name(previous)}_valid (Eq.refl true)\n\n')
            else:
                output.append(f'  exact {qualified}Valid.pow {name(node)}.normal {name(node[1])} {node[2]} {name(node[1])}_valid (Eq.refl true)\n\n')
        elif local_checks:
            output.append(f'private theorem {name(node)}_ok : {name(node)}.check=true := by\n')
            if kind in ('coeff','x','t'):
                output.append('  rfl\n\n')
            elif kind in ('plus','times'):
                output.append(f'  exact {qualified}check_{kind} {name(node)}.normal {name(node[1])} {name(node[2])}\n')
                output.append(f'    {name(node[1])}_ok {name(node[2])}_ok (by rfl)\n\n')
            elif kind=='neg':
                output.append(f'  exact {qualified}check_neg {name(node)}.normal {name(node[1])} {name(node[1])}_ok (by rfl)\n\n')
            else:
                output.append(f'  exact {qualified}check_pow {name(node)}.normal {name(node[1])} {node[2]} {name(node[1])}_ok (by rfl)\n\n')
    assert normal(lhs)==normal(rhs), 'Generated integer normal forms differ'
    if validity:
        output.append(f'private theorem {prefix}_checked :\n    decide ({name(lhs)}.normal={name(rhs)}.normal)=true := Eq.refl true\n\n')
    else:
        output.append(f'private theorem {prefix}_checked :\n    {qualified}checkIdentity {name(lhs)} {name(rhs)}=true := by\n')
    if validity:
        pass
    elif local_checks:
        output.append(f'  exact {qualified}checkIdentity_of_checks {name(lhs)} {name(rhs)} {name(lhs)}_ok {name(rhs)}_ok (by rfl)\n\n')
    else:
        output.append('  rfl\n\n')
    return ''.join(output),name(lhs),name(rhs),[name(node) for node in nodes]


def lower_powers(expression):
    """Match SparseProgram.lowerPowers, including its left-associated powers."""
    kind = expression[0]
    if kind == 'pow':
        base = lower_powers(expression[1])
        result = ('coeff',1)
        for _ in range(expression[2]):
            result = ('times',result,base)
        return result
    if kind == 'neg':
        return (kind,lower_powers(expression[1]))
    if kind in ('plus','times'):
        return (kind,lower_powers(expression[1]),lower_powers(expression[2]))
    return expression


def accumulator_product_certificate(left_poly, right_poly, target_poly,
                                    left_expr, right_expr, target_expr,
                                    prefix, row_chunk_size, fast_product_guards=False,
                                    kernel_decide=False):
    """Prove one exact legacy product from bounded right-associated row groups.

    Proposed suffixes are plain constructor data. Every substitution requires
    its own closed kernel guard, and the append theorem preserves the original
    addition order without an associativity or sorting assumption.
    """
    assert row_chunk_size > 0 and min(len(left_poly), len(right_poly)) >= 2
    left_is_rows = len(left_poly) <= len(right_poly)
    rows, factor = (left_poly, right_poly) if left_is_rows else (right_poly, left_poly)
    boundaries = list(range(0, len(rows), row_chunk_size)) + [len(rows)]
    suffixes = {len(rows): []}
    normal = {}
    for index in reversed(range(len(rows))):
        i, j, coefficient = rows[index]
        for k, l, other in factor:
            key = (i + k, j + l)
            normal[key] = normal.get(key, 0) + int(coefficient) * int(other)
        if index in boundaries:
            suffixes[index] = [[i, j, str(c)] for (i, j), c in sorted(normal.items()) if c]
    assert suffixes[0] == target_poly, 'Proposed product suffix differs from original cache'
    aq = 'CertificateKernel.SparseProductAccumulator.'
    guard_aq = 'CertificateKernel.SparseProductAccumulatorFast.' if fast_product_guards else aq
    guard_to_equality = guard_aq + ('original_mulAcc_eq_of_beq' if fast_product_guards else 'mulAcc_eq_of_beq')
    guard_proof = 'by decide +kernel' if kernel_decide else 'Eq.refl true'
    poly = 'CertificateKernel.SparsePolynomial.Poly'
    out = [f'private noncomputable def {prefix}_left : {poly} := {left_expr}\n\n',
           f'private noncomputable def {prefix}_right : {poly} := {right_expr}\n\n',
           f'private noncomputable def {prefix}_result : {poly} := {target_expr}\n\n']
    rows_expr = prefix + ('_left' if left_is_rows else '_right')
    factor_expr = prefix + ('_right' if left_is_rows else '_left')
    middle = boundaries[1:-1]
    if middle:
        # The opcodes of this auxiliary holder are unused. Its literal caches
        # acquire proof significance only through the guarded equalities below.
        encoded = [[0, ['0'], suffixes[index]] for index in middle]
        payload = json.dumps(json.dumps(encoded, separators=(',', ':')))
        out.append(f'private noncomputable def {prefix}_suffix_data : CertificateKernel.SparseProgramArray.Certificate :=\n'
                   f'  sparse_program_array_literal% {payload}\n\n')

    def state(index):
        if index == 0:
            return prefix + '_result'
        if index + 1 == len(boundaries):
            return '[]'
        return f'({prefix}_suffix_data.caches.get {index-1})'

    chunks = []
    for index, (start, end) in enumerate(zip(boundaries, boundaries[1:])):
        name = f'{prefix}_rows_chunk{index:04d}'
        chunks.append(name)
        out.append(f'private noncomputable def {name} : {poly} :=\n'
                   f'  ({rows_expr}.drop {start}).take {end-start}\n\n')
        out.append(f'private theorem {name}_checked :\n'
                   f'    ({guard_aq}mulAcc {name} {factor_expr} {state(index+1)} == {state(index)})=true := {guard_proof}\n\n')
        out.append(f'private theorem {name}_eq :\n'
                   f'    {aq}mulAcc {name} {factor_expr} {state(index+1)}={state(index)} :=\n'
                   f'  {guard_to_equality} {name} {factor_expr} {state(index+1)} {state(index)} {name}_checked\n\n')
    for index in reversed(range(len(chunks))):
        name = chunks[index]
        suffix = f'{prefix}_rows_suffix{index:04d}'
        if index + 1 == len(chunks):
            out.append(f'private noncomputable def {suffix} : {poly} := {name}\n\n')
            out.append(f'private theorem {suffix}_eq :\n'
                       f'    {aq}mulAcc {suffix} {factor_expr} []={state(index)} := {name}_eq\n\n')
        else:
            following = f'{prefix}_rows_suffix{index+1:04d}'
            out.append(f'private noncomputable def {suffix} : {poly} := {name} ++ {following}\n\n')
            out.append(f'private theorem {suffix}_eq :\n'
                       f'    {aq}mulAcc {suffix} {factor_expr} []={state(index)} :=\n'
                       f'  {aq}mulAcc_append_of_eq {name} {following} {factor_expr} [] {state(index+1)} {state(index)}\n'
                       f'    {following}_eq {name}_eq\n\n')
    out.append(f'private theorem {prefix}_rows_eq : {rows_expr}={prefix}_rows_suffix0000 := rfl\n\n')
    out.append(f'private theorem {prefix}_acc_eq :\n'
               f'    {aq}mulAcc {rows_expr} {factor_expr} []={prefix}_result :=\n'
               f'  (congrArg (fun rows => {aq}mulAcc rows {factor_expr} []) {prefix}_rows_eq).trans\n'
               f'    {prefix}_rows_suffix0000_eq\n\n')
    orientation = 'le' if left_is_rows else 'gt'
    theorem = prefix + '_mul_eq'
    out.append(f'private theorem {theorem} :\n'
               f'    CertificateKernel.SparseProgram.mulFast {prefix}_left {prefix}_right={prefix}_result :=\n'
               f'  {aq}mulFast_eq_of_mulAcc_{orientation} {prefix}_left {prefix}_right {prefix}_result\n'
               f'    (by decide) (by decide) (by decide) {prefix}_acc_eq\n\n')
    return ''.join(out), theorem


def program_certificate(lhs,rhs,prefix,explicit_integers=False,program_chunk_size=0,literal=False,fast_program=False,array_program=False,array_chunk_size=0,balanced_array=False,product_row_chunk_size=0,product_pair_threshold=4096,fast_product_guards=False,fast_array_guards=False,kernel_decide=False,array_aliases=False):
    """Emit one instruction stream and a kernel-checked local-cache guard."""
    nodes,indices,normals=[],{},{}
    left,right=lower_powers(lhs),lower_powers(rhs)

    def visit(node):
        if node in indices:
            return
        kind=node[0]
        if kind=='neg':
            visit(node[1])
        elif kind in ('plus','times'):
            visit(node[1]); visit(node[2])
        if kind=='coeff':
            result={(0,0):node[1]} if node[1] else {}
        elif kind=='x':
            result={(1,0):1}
        elif kind=='t':
            result={(0,1):1}
        elif kind=='neg':
            result={m:-c for m,c in normals[node[1]].items()}
        elif kind=='plus':
            result=normals[node[1]].copy()
            for m,c in normals[node[2]].items():
                result[m]=result.get(m,0)+c
        elif kind=='times':
            result={}
            for (i,j),c in normals[node[1]].items():
                for (k,l),d in normals[node[2]].items():
                    m=(i+k,j+l)
                    result[m]=result.get(m,0)+c*d
        else:
            raise ValueError(f'Unexpected lowered operator {kind}')
        indices[node]=len(nodes)
        nodes.append(node)
        normals[node]={m:c for m,c in result.items() if c}

    visit(left); visit(right)
    assert normals[left]==normals[right], 'Generated integer normal forms differ'
    qualified='CertificateKernel.'+('SparseProgramArrayBalanced' if balanced_array else ('SparseProgramArray' if array_program else 'SparseProgram'))+'.'
    def integer(n):
        if not explicit_integers:
            return str(n)
        return f'(Int.ofNat {n})' if n>=0 else f'(Int.negSucc {-n-1})'
    entries=[]
    encoded=[]
    for index,node in enumerate(nodes):
        kind=node[0]
        ref=lambda child:index-1-indices[child]
        if kind=='coeff':
            op=f'.coeff {integer(node[1])}'
        elif kind in ('x','t'):
            op='.'+kind
        elif kind=='neg':
            op=f'.neg {ref(node[1])}'
        else:
            op=f'.{kind} {ref(node[1])} {ref(node[2])}'
        cache='['+','.join(f'(({i},{j}),{integer(c)})' for (i,j),c in sorted(normals[node].items()))+']'
        entries.append(f'  {{ op := {op}, cache := {cache} }}')
        opcode={'coeff':0,'x':1,'t':2,'plus':3,'times':4,'neg':5}[kind]
        operands=([str(node[1])] if kind=='coeff' else
                  [ref(node[1]),ref(node[2])] if kind in ('plus','times') else
                  [ref(node[1])] if kind=='neg' else [])
        encoded.append([opcode,operands,[[i,j,str(c)] for (i,j),c in sorted(normals[node].items())]])
    out=[]
    if literal:
        payload=json.dumps(json.dumps(encoded,separators=(',',':')))
        data_type = 'Certificate' if array_program else 'Program'
        literal_name = 'sparse_program_array_literal' if array_program else 'sparse_program_literal'
        out.append(f'private noncomputable def {prefix}_program : {qualified}{data_type} :=\n  {literal_name}% {payload}\n\n')
    elif program_chunk_size:
        chunks=[]
        for start in range(0,len(entries),program_chunk_size):
            name=f'{prefix}_program_chunk{start//program_chunk_size:04d}'
            chunks.append(name)
            out.append(f'private noncomputable def {name} : {qualified}Program := [\n'+',\n'.join(entries[start:start+program_chunk_size])+'\n]\n\n')
        def append_tree(names):
            if len(names)==1:
                return names[0]
            middle=len(names)//2
            return f'({append_tree(names[:middle])} ++ {append_tree(names[middle:])})'
        out.append(f'private noncomputable def {prefix}_program : {qualified}Program := {append_tree(chunks)}\n\n')
    else:
        out.append(f'private noncomputable def {prefix}_program : {qualified}Program := [\n'+',\n'.join(entries)+'\n]\n\n')
    product_helpers = {}
    if product_row_chunk_size:
        for index, (opcode, operands, target) in enumerate(encoded):
            if opcode != 4:
                continue
            left_ref, right_ref = operands
            left_poly = encoded[index-1-left_ref][2]
            right_poly = encoded[index-1-right_ref][2]
            if min(len(left_poly), len(right_poly)) < 2 or len(left_poly)*len(right_poly) < product_pair_threshold:
                continue
            left_expr = f'{qualified}readCache {prefix}_program.caches {index} {left_ref}'
            right_expr = f'{qualified}readCache {prefix}_program.caches {index} {right_ref}'
            target_expr = f'{prefix}_program.caches.get {index}'
            helper, theorem = accumulator_product_certificate(left_poly, right_poly, target,
                left_expr, right_expr, target_expr, f'{prefix}_product{index:04d}', product_row_chunk_size, fast_product_guards, kernel_decide)
            out.append(helper)
            product_helpers[index] = (left_ref, right_ref, theorem)
    checker = 'checkFast' if fast_program else 'check'
    guard_proof = 'by decide +kernel' if kernel_decide else 'Eq.refl true'
    if array_chunk_size:
        chunks = []
        if product_helpers:
            boundaries = set(range(0, len(nodes), array_chunk_size)) | {len(nodes)}
            for index in product_helpers:
                boundaries.update((index, index+1))
            boundaries = sorted(boundaries)
            segments = [(start, end-start) for start, end in zip(boundaries, boundaries[1:])]
        else:
            segments = [(start, array_chunk_size) for start in range(0, len(nodes), array_chunk_size)]
        for index, (start, size) in enumerate(segments):
            name = f'{prefix}_ops_chunk{index:04d}'
            chunks.append((start, name))
            out.append(f'private noncomputable def {name} : List CertificateKernel.SparseProgram.Op :=\n'
                       f'  ({prefix}_program.ops.drop {start}).take {size}\n\n')
            if start in product_helpers:
                assert size == 1
                left_ref, right_ref, theorem = product_helpers[start]
                product_prefix = theorem.removesuffix('_mul_eq')
                out.append(f'private theorem {name}_checked :\n'
                           f'    {qualified}checkFrom {prefix}_program.caches {start} {name}=true :=\n')
                if array_aliases:
                    out.append(f'  CertificateKernel.SparseProgramArrayAliases.checkFrom_of_ops_eq\n'
                               f'    {prefix}_program.caches {start} {name} [.times {left_ref} {right_ref}]\n'
                               f'    (Eq.refl [CertificateKernel.SparseProgram.Op.times {left_ref} {right_ref}])\n'
                               f'    ({qualified}checkFrom_times_singleton_of_operand_eq {prefix}_program.caches {start} {left_ref} {right_ref}\n'
                               f'      {product_prefix}_left {product_prefix}_right {product_prefix}_result\n'
                               f'      rfl rfl rfl {theorem})\n\n')
                else:
                    out.append(f'  {qualified}checkFrom_times_singleton_of_operand_eq {prefix}_program.caches {start} {left_ref} {right_ref}\n'
                               f'    {product_prefix}_left {product_prefix}_right {product_prefix}_result\n'
                               f'    rfl rfl rfl {theorem}\n\n')
            elif fast_array_guards:
                out.append(f'private theorem {name}_checked :\n'
                           f'    {qualified}checkFrom {prefix}_program.caches {start} {name}=true :=\n'
                           f'  CertificateKernel.SparseProgramArrayNoFuel.original_checkFrom_eq_of_check\n'
                           f'    {prefix}_program.caches {start} {name} ({guard_proof})\n\n')
            else:
                out.append(f'private theorem {name}_checked :\n'
                           f'    {qualified}checkFrom {prefix}_program.caches {start} {name}=true := {guard_proof}\n\n')
        for index in reversed(range(len(chunks))):
            start, name = chunks[index]
            suffix = f'{prefix}_ops_suffix{index:04d}'
            if index + 1 == len(chunks):
                out.append(f'private noncomputable def {suffix} : List CertificateKernel.SparseProgram.Op := {name}\n\n')
                out.append(f'private theorem {suffix}_checked :\n'
                           f'    {qualified}checkFrom {prefix}_program.caches {start} {suffix}=true := ')
                if array_aliases:
                    out.append(f'\n  CertificateKernel.SparseProgramArrayAliases.checkFrom_of_ops_eq\n'
                               f'    {prefix}_program.caches {start} {suffix} {name} (Eq.refl {name}) {name}_checked\n\n')
                else:
                    out.append(f'{name}_checked\n\n')
            else:
                following = f'{prefix}_ops_suffix{index+1:04d}'
                out.append(f'private noncomputable def {suffix} : List CertificateKernel.SparseProgram.Op := {name} ++ {following}\n\n')
                out.append(f'private theorem {suffix}_checked :\n'
                           f'    {qualified}checkFrom {prefix}_program.caches {start} {suffix}=true :=\n')
                if array_aliases:
                    next_index = chunks[index+1][0]
                    out.append(f'  CertificateKernel.SparseProgramArrayAliases.checkFrom_append_of_ops_eq\n'
                               f'    {prefix}_program.caches {start} {next_index} {suffix} {name} {following}\n'
                               f'    (Eq.refl ({name} ++ {following})) (Eq.refl {next_index})\n'
                               f'    {name}_checked {following}_checked\n\n')
                else:
                    out.append(f'  {qualified}checkFrom_append_eq_true {prefix}_program.caches {start} {name} {following}\n'
                               f'    {name}_checked {following}_checked\n\n')
        first_suffix = f'{prefix}_ops_suffix0000'
        if array_aliases:
            out.append(f'private theorem {prefix}_checked : {qualified}check {prefix}_program=true :=\n'
                       f'  CertificateKernel.SparseProgramArrayAliases.check_of_ops_eq\n'
                       f'    {prefix}_program {first_suffix} (Eq.refl {first_suffix}) {first_suffix}_checked\n\n')
        else:
            out.append(f'private theorem {prefix}_checked : {qualified}check {prefix}_program=true := by\n'
                       f'  change {qualified}checkFrom {prefix}_program.caches 0 {prefix}_program.ops=true\n'
                       f'  have hop : {prefix}_program.ops={first_suffix} := rfl\n'
                       f'  rw [hop]\n'
                       f'  exact {first_suffix}_checked\n\n')
    else:
        out.append(f'private theorem {prefix}_checked : {qualified}{checker} {prefix}_program=true := {guard_proof}\n\n')
    i,j=len(nodes)-1-indices[left],len(nodes)-1-indices[right]
    out.append(f'private theorem {prefix}_root_eq :\n    decide ({qualified}outputCache {prefix}_program {i}={qualified}outputCache {prefix}_program {j})=true := {guard_proof}\n\n')
    return ''.join(out),i,j,len(nodes)


def compact(text, definitions, dag=False, node_budget=0, certificate=False, local_checks=False, validity=False, sparse=False, program=False,explicit_integers=False,program_chunk_size=0,literal=False,source_value=False,fast_program=False,array_program=False,array_chunk_size=0,split_kernel_module=None,balanced_array=False,product_row_chunk_size=0,product_pair_threshold=4096,fast_product_guards=False,fast_array_guards=False,kernel_decide=False,array_aliases=False):
    matcher = re.compile(r'^theorem (\w+) \((\w+) (\w+) : ℝ\) :\s*(.*?) := by\n(.*?)(?=^theorem\b|^end\b|\Z)', re.M | re.S)
    replacements = []
    kernel_sections = []
    kernel_options = re.findall(r'^set_option [^\n]+$', text, re.M)
    for match in matcher.finditer(text):
        name, first, second, equation, proof = match.groups()
        if not name.endswith(('_identity', '_map')) or '=' not in equation:
            continue
        # These modules are generated as polynomial equalities.  Conditional
        # analytic lemmas and positivity proofs are deliberately not selected.
        left, right = equation.split('=', 1)
        definitions.used = set()
        definitions.cache = {}
        variables = {first: ('x',), second: ('t',)}
        lhs = definitions.expression(left, variables)
        rhs = definitions.expression(right, variables)
        used = sorted(definitions.used)
        prefix = name + '_kernel'
        if program:
            additions,left_index,right_index,_=program_certificate(lhs,rhs,prefix,explicit_integers,program_chunk_size,literal,fast_program,array_program,array_chunk_size,balanced_array,product_row_chunk_size,product_pair_threshold,fast_product_guards,fast_array_guards,kernel_decide,array_aliases)
            identity_helper = 'identity_of_checkFast' if fast_program else 'identity_of_check'
            program_namespace = 'SparseProgramArrayBalanced' if balanced_array else ('SparseProgramArray' if array_program else 'SparseProgram')
            lhs_name=f'CertificateKernel.{program_namespace}.outputExpr {prefix}_program {left_index}'
            rhs_name=f'CertificateKernel.{program_namespace}.outputExpr {prefix}_program {right_index}'
            additions+=f'''private noncomputable def {prefix}_plain_left : CertificateKernel.DensePolynomial.Expr := {lean(lhs)}

private noncomputable def {prefix}_plain_right : CertificateKernel.DensePolynomial.Expr := {lean(rhs)}

private theorem {prefix}_erase_left : {lhs_name}=CertificateKernel.SparseProgram.lowerPowers {prefix}_plain_left :=
  Eq.refl (CertificateKernel.SparseProgram.lowerPowers {prefix}_plain_left)

private theorem {prefix}_erase_right : {rhs_name}=CertificateKernel.SparseProgram.lowerPowers {prefix}_plain_right :=
  Eq.refl (CertificateKernel.SparseProgram.lowerPowers {prefix}_plain_right)

'''
            helper_name = name + '_source_value'
            if split_kernel_module:
                additions += f'''theorem {helper_name} ({first} {second} : ℝ) :
    CertificateKernel.SourceValue.value {first} {second} {prefix}_plain_left =
      CertificateKernel.SourceValue.value {first} {second} {prefix}_plain_right := by
'''
            else:
                additions += f'''theorem {name} ({first} {second} : ℝ) :
    {equation} := by
'''
            additions += f'''\
  have he := CertificateKernel.{program_namespace}.{identity_helper}
    {prefix}_program {prefix}_checked {left_index} {right_index} {prefix}_root_eq {first} {second}
  rw [{prefix}_erase_left,{prefix}_erase_right,
    CertificateKernel.SparseProgram.value_lowerPowers,CertificateKernel.SparseProgram.value_lowerPowers] at he
'''
            if source_value:
                additions+=f'''  exact CertificateKernel.SourceValue.identity_of_value_eq
    {prefix}_plain_left {prefix}_plain_right {first} {second} he

'''
            else:
                additions+=f'''  simpa only [{prefix}_plain_left,{prefix}_plain_right,CertificateKernel.DensePolynomial.Expr.value,
    sub_eq_add_neg,Int.cast_ofNat,Int.cast_neg,Int.cast_zero,Int.cast_one'''
                if used:
                    additions+=','+','.join(used)
                additions+='] using he\n\n'
            if split_kernel_module:
                kernel_sections.append(additions)
                additions = f'''theorem {name} ({first} {second} : ℝ) :
    {equation} := by
  exact {helper_name} {first} {second}

'''
            replacements.append((match.start(),match.end(),additions))
            continue
        elif certificate:
            additions,lhs_name,rhs_name,expression_defs=cached_tree_certificate(lhs,rhs,prefix,local_checks,validity,sparse)
        elif dag:
            additions, lhs_name, rhs_name, expression_defs = dag_certificate(lhs, rhs, prefix, node_budget)
        else:
            lhs_name, rhs_name = prefix + '_left', prefix + '_right'
            expression_defs = [lhs_name, rhs_name]
            additions = f'''private noncomputable def {prefix}_left : CertificateKernel.DensePolynomial.Expr := {lean(lhs)}

private noncomputable def {prefix}_right : CertificateKernel.DensePolynomial.Expr := {lean(rhs)}

private theorem {prefix}_checked :
    decide ({prefix}_left.normal={prefix}_right.normal)=true := by
  rfl

'''
        if validity:
            additions += f'''private noncomputable def {prefix}_plain_left : CertificateKernel.DensePolynomial.Expr := {lean(lhs)}

private noncomputable def {prefix}_plain_right : CertificateKernel.DensePolynomial.Expr := {lean(rhs)}

private theorem {prefix}_erase_left : {lhs_name}.expr={prefix}_plain_left := Eq.refl {prefix}_plain_left

private theorem {prefix}_erase_right : {rhs_name}.expr={prefix}_plain_right := Eq.refl {prefix}_plain_right

'''
            expression_defs=[prefix+'_plain_left',prefix+'_plain_right']
        certificate_namespace = 'CertificateKernel.'+('SparsePolynomial' if sparse else 'PolynomialDAG')
        theorem_helper = certificate_namespace+'.identity_of_valid' if validity else ('CertificateKernel.PolynomialDAG.identity_of_checkIdentity' if certificate else 'CertificateKernel.DensePolynomial.identity_of_normal_eq_true')
        interpreter = 'CertificateKernel.PolynomialDAG.Cert.expr,' if certificate else ''
        arguments=f'{lhs_name} {rhs_name} '+(f'{lhs_name}_valid {rhs_name}_valid ' if validity else '')+f'{prefix}_checked {first} {second}'
        additions += f'''theorem {name} ({first} {second} : ℝ) :
    {equation} := by
  have he := {theorem_helper}
    {arguments}
'''
        if validity:
            additions += f'''  have hp : {prefix}_plain_left.value {first} {second}={prefix}_plain_right.value {first} {second} :=
    (congrArg (fun e : CertificateKernel.DensePolynomial.Expr => e.value {first} {second}) {prefix}_erase_left.symm).trans
      (he.trans (congrArg (fun e : CertificateKernel.DensePolynomial.Expr => e.value {first} {second}) {prefix}_erase_right))
'''
            interpreter=''
        additions += '  simpa only [' + ','.join(expression_defs) + f''',{interpreter}CertificateKernel.DensePolynomial.Expr.value,
    sub_eq_add_neg,Int.cast_ofNat,Int.cast_neg,Int.cast_zero,Int.cast_one'''
        if used:
            additions += ',' + ','.join(used)
        additions += '] using '+('hp' if validity else 'he')+'\n\n'
        replacements.append((match.start(), match.end(), additions))
    for start, end, replacement in reversed(replacements):
        text = text[:start] + replacement + text[end:]
    kernel_text = None
    if replacements:
        dependency = ('SparseProgramArrayLiteral' if array_program else ('SparseProgramLiteral' if literal else 'SparseProgram')) if program else ('SparsePolynomial' if sparse else ('PolynomialDAG' if certificate else 'DensePolynomial'))
        imports = f'import LeanVerification.CertificateKernel.{dependency}\n'
        if source_value:
            imports = 'import LeanVerification.CertificateKernel.SourceValue\n' + imports
        if fast_program:
            imports = 'import LeanVerification.CertificateKernel.SparseProgramFast\n' + imports
        if array_chunk_size and not balanced_array:
            imports = 'import LeanVerification.CertificateKernel.SparseProgramArrayChunks\n' + imports
        if balanced_array:
            imports = 'import LeanVerification.CertificateKernel.SparseProgramArrayBalanced\n' + imports
        if product_row_chunk_size:
            imports = ('import LeanVerification.CertificateKernel.SparseProductAccumulator\n'
                       'import LeanVerification.CertificateKernel.SparseProgramArrayProductStep\n' + imports)
        if fast_product_guards:
            imports = 'import LeanVerification.CertificateKernel.SparseProductAccumulatorFast\n' + imports
        if fast_array_guards:
            imports = 'import LeanVerification.CertificateKernel.SparseProgramArrayNoFuel\n' + imports
        if array_aliases:
            imports = 'import LeanVerification.CertificateKernel.SparseProgramArrayAliases\n' + imports
        if split_kernel_module:
            kernel_text = (imports + '\nnoncomputable section\n'
                'namespace LeanVerification.PositiveDCompletion\n'
                'set_option Elab.async false\n' + '\n'.join(kernel_options) + '\n\n'
                + ''.join(kernel_sections) + 'end LeanVerification.PositiveDCompletion\n')
            text = f'import {split_kernel_module}\n' + text
        else:
            text = imports + text
        text = text.replace('namespace LeanVerification.PositiveDCompletion\n', 'namespace LeanVerification.PositiveDCompletion\nset_option Elab.async false\n', 1)
    return text, len(replacements), kernel_text


def split_kernel_phases(kernel_text, kernel_module):
    """Separate one exact certificate into independently checked proof phases.

    The seven shared declarations retain their existing globally unique names,
    types and bodies; only their private visibility is removed. In particular,
    neither erase proof imports the arithmetic guards. The final theorem uses
    a generic composition lemma with every original obligation explicit.
    """
    declaration = re.compile(r'^(?:private )?(?:noncomputable )?(?:def|theorem) (\w+)\b', re.M)
    matches = list(declaration.finditer(kernel_text))
    if not matches:
        raise ValueError('A phase split needs a generated kernel declaration')
    ending = 'end LeanVerification.PositiveDCompletion\n'
    if not kernel_text.endswith(ending):
        raise ValueError('Unexpected generated kernel namespace ending')
    records = [(match[1], kernel_text[match.start():matches[index+1].start()
                if index+1 < len(matches) else len(kernel_text)-len(ending)])
               for index, match in enumerate(matches)]
    by_name = dict(records)
    if len(by_name) != len(records):
        raise ValueError('Generated declaration names must be unique')
    program_names = [name for name in by_name if name.endswith('_kernel_program')]
    if len(program_names) != 1:
        raise ValueError('A phase split currently requires exactly one identity')
    prefix = program_names[0].removesuffix('_program')
    identity = prefix.removesuffix('_kernel') + '_source_value'
    data_names = [prefix + suffix for suffix in ('_program', '_plain_left', '_plain_right')]
    erase_names = [prefix + suffix for suffix in ('_erase_left', '_erase_right')]
    guard_exports = [prefix + suffix for suffix in ('_checked', '_root_eq')]
    required = data_names + erase_names + guard_exports + [identity]
    if any(name not in by_name for name in required):
        raise ValueError('Missing required exact certificate obligation')
    if any(not name.startswith(prefix + '_') and name != identity for name in by_name):
        raise ValueError('Unexpected declaration outside the one-identity prefix')
    final_match = re.fullmatch(r'theorem (\w+) \((\w+) (\w+) : ℝ\) :(.*?) := by\n(.*)',
                              by_name[identity], re.S)
    if not final_match or final_match[1] != identity:
        raise ValueError('Unexpected generated SourceValue theorem shape')
    first, second = final_match[2], final_match[3]
    output_indices = re.findall(
        rf'CertificateKernel\.SparseProgramArray\.outputCache {re.escape(prefix)}_program (\d+)',
        by_name[prefix + '_root_eq'])
    if len(output_indices) != 2:
        raise ValueError('A phase split retains the original array output-cache check')
    left_index, right_index = output_indices
    header = kernel_text[:matches[0].start()]
    imports = re.findall(r'^import [^\n]+\n', header, re.M)
    prelude = re.sub(r'^import [^\n]+\n', '', header, flags=re.M).lstrip('\n')

    def exported(name):
        source = by_name[name]
        if not source.startswith('private '):
            raise ValueError(f'Expected a private shared helper: {name}')
        return source.removeprefix('private ')

    def module_text(selected_imports, body):
        return ''.join(selected_imports) + '\n' + prelude + body + ending

    stem = kernel_module.rsplit('.', 1)[-1]
    data_module, guards_module, erase_module = [kernel_module + part for part in ('Data', 'Guards', 'Erase')]
    data_import = f'import {data_module}\n'
    data_text = module_text(['import LeanVerification.CertificateKernel.SparseProgramArrayLiteral\n'],
                            ''.join(exported(name) for name in data_names))
    guard_body = ''.join(exported(name) if name in guard_exports else source
                         for name, source in records
                         if name not in data_names + erase_names + [identity])
    guards_text = module_text([data_import] + imports, guard_body)
    erase_text = module_text([data_import], ''.join(exported(name) for name in erase_names))
    final_signature = by_name[identity].split(' := by\n', 1)[0]
    final_body = f'''{final_signature} := by
  exact CertificateKernel.sourceIdentity_of_checked
    {prefix}_program {prefix}_plain_left {prefix}_plain_right {left_index} {right_index}
    {prefix}_checked {prefix}_root_eq {prefix}_erase_left {prefix}_erase_right {first} {second}

'''
    final_text = module_text([f'import {guards_module}\n', f'import {erase_module}\n',
                             'import LeanVerification.CertificateKernel.SourceIdentity\n'], final_body)
    return {stem + 'Data': data_text, stem + 'Guards': guards_text,
            stem + 'Erase': erase_text, stem: final_text}


def split_guard_units(phase_files, kernel_module, theorems_per_module):
    """Partition unchanged guard declarations into bounded compilation units.

    Data-only definitions are shared. Each proof unit imports its exact
    declaration dependencies, and only names used by another file lose their
    private modifier. No theorem proposition, proof body, or data body changes.
    """
    if theorems_per_module < 1:
        raise ValueError('A guard unit needs a positive theorem bound')
    stem = kernel_module.rsplit('.', 1)[-1]
    guard_name = stem + 'Guards'
    text = phase_files[guard_name]
    pattern = re.compile(r'^(private )?(noncomputable )?(def|theorem) (\w+)\b', re.M)
    matches = list(pattern.finditer(text))
    ending = 'end LeanVerification.PositiveDCompletion\n'
    if not matches or not text.endswith(ending):
        raise ValueError('Unexpected generated guard module')
    records = [(m[4], m[3], text[m.start():matches[i+1].start()
                if i+1 < len(matches) else len(text)-len(ending)])
               for i, m in enumerate(matches)]
    declarations = {name: (kind, body) for name, kind, body in records}
    if len(declarations) != len(records):
        raise ValueError('Guard declaration identifiers must be distinct')
    final_names = [name for name, kind, body in records if not body.startswith('private ')]
    if len(final_names) != 2 or not final_names[0].endswith('_kernel_checked') or not final_names[1].endswith('_kernel_root_eq'):
        raise ValueError('Expected the two original exported guard obligations')
    data_name = stem + 'GuardData'
    proof_names = [name for name, kind, body in records if kind == 'theorem' and name not in final_names]
    proof_units = [stem + f'GuardProof{i:04d}'
                   for i in range((len(proof_names) + theorems_per_module - 1) // theorems_per_module)]
    owner = {name: data_name for name, kind, body in records if kind == 'def'}
    owner.update({name: proof_units[i // theorems_per_module] for i, name in enumerate(proof_names)})
    owner.update({name: guard_name for name in final_names})
    all_names = set(declarations)
    references = {name: (set(re.findall(r'\b[A-Za-z_][A-Za-z_0-9]*\b', body)) & all_names) - {name}
                  for name, kind, body in records}
    source_index = {name: i for i, (name, kind, body) in enumerate(records)}
    for name, kind, body in records:
        if any(source_index[dependency] >= source_index[name] for dependency in references[name]):
            raise ValueError(f'Unexpected forward guard declaration reference in {name}')
        if kind == 'def' and any(declarations[dependency][0] != 'def' for dependency in references[name]):
            raise ValueError(f'Guard data depends on a proof in {name}')
    exported = {dependency for name in all_names for dependency in references[name]
                if owner[dependency] != owner[name]}
    exported.update(final_names)
    header = text[:matches[0].start()]
    namespace_prefix = kernel_module.rsplit('.', 1)[0]
    outputs = {name: contents for name, contents in phase_files.items() if name != guard_name}
    for target in [data_name] + proof_units + [guard_name]:
        selected = [(name, kind, body) for name, kind, body in records if owner[name] == target]
        dependency_units = sorted({owner[dependency] for name, kind, body in selected
                                   for dependency in references[name] if owner[dependency] != target})
        new_imports = ''.join(f'import {namespace_prefix}.{dependency}\n' for dependency in dependency_units)
        body = ''.join(source.removeprefix('private ') if name in exported else source
                       for name, kind, source in selected)
        outputs[target] = new_imports + header + body + ending
    return outputs


def add_array_coverage(phase_files, kernel_module):
    """Prove exact slice coverage without a global closed-list conversion.

    Every existing program, slice, suffix, arithmetic guard and source proof
    stays byte-identical. Only the final checker proof's list-equality argument
    is replaced by a theorem about the same complete operation list.
    """
    stem = kernel_module.rsplit('.', 1)[-1]
    namespace = kernel_module.rsplit('.', 1)[0]
    guards = phase_files[stem + 'Guards']
    data = phase_files[stem + 'GuardData']
    programs = re.findall(r'theorem (\w+_kernel)_checked : CertificateKernel\.SparseProgramArray\.check (\w+)=true', guards)
    if len(programs) != 1:
        raise ValueError('Coverage needs the one original array checker obligation')
    prefix, program = programs[0]
    if program != prefix + '_program':
        raise ValueError('Unexpected program name in the checker obligation')
    literals = re.findall(r'sparse_program_array_literal%\s+("(?:\\.|[^"\\])*")',
                          phase_files[stem + 'Data'])
    if len(literals) != 1:
        raise ValueError('Coverage needs the one unchanged constructor-only program literal')
    nodes = json.loads(json.loads(literals[0]))
    if not isinstance(nodes, list) or not nodes:
        raise ValueError('Coverage needs a nonempty exact operation stream')
    total = len(nodes)
    chunks = re.findall(
        rf'^noncomputable def ({re.escape(prefix)}_ops_chunk(\d{{4}})) : List CertificateKernel\.SparseProgram\.Op :=\n'
        rf'  \({re.escape(program)}\.ops\.drop (\d+)\)\.take (\d+)\n', data, re.M)
    suffixes = re.findall(
        rf'^noncomputable def ({re.escape(prefix)}_ops_suffix(\d{{4}})) : List CertificateKernel\.SparseProgram\.Op := ([^\n]+)\n', data, re.M)
    if len(chunks) != len(suffixes) or not chunks:
        raise ValueError('Coverage needs every existing contiguous slice and suffix')
    chunks = sorted(chunks, key=lambda row: int(row[1]))
    suffixes = sorted(suffixes, key=lambda row: int(row[1]))
    offset = 0
    for index, (chunk, number, start, size) in enumerate(chunks):
        if int(number) != index or int(start) != offset or int(size) < 1:
            raise ValueError('Operation slices must be consecutive and nonempty')
        suffix, suffix_number, body = suffixes[index]
        expected = chunk if index + 1 == len(chunks) else chunk + ' ++ ' + suffixes[index + 1][0]
        if int(suffix_number) != index or body != expected:
            raise ValueError('Unexpected original suffix-concatenation definition')
        offset += int(size)
    if offset != total:
        raise ValueError('Slices must cover exactly the original operation count')
    coverage_name = stem + 'Coverage'
    options = '\n'.join(re.findall(r'^set_option [^\n]+$', guards, re.M))
    out = [f'import {namespace}.{stem}GuardData\n',
           'import LeanVerification.CertificateKernel.SparseProgramArrayCoverage\n\n',
           'noncomputable section\nnamespace LeanVerification.PositiveDCompletion\n', options + '\n\n',
           f'private theorem {prefix}_ops_length : {program}.ops.length={total} := by decide +kernel\n\n']
    helper = 'CertificateKernel.SparseProgramArrayCoverage.'
    for index in reversed(range(len(chunks))):
        chunk, number, start, size = chunks[index]
        start, size = int(start), int(size)
        suffix = suffixes[index][0]
        out.append(f'private theorem {suffix}_coverage :\n    {suffix}={program}.ops.drop {start} :=\n')
        if index + 1 == len(chunks):
            out.append(f'  {helper}final_suffix_eq_drop\n    {program}.ops {start} {size} {total} {chunk} {suffix}\n'
                       f'    {prefix}_ops_length (Eq.refl {total}) (Eq.refl {chunk}) (Eq.refl {chunk})\n\n')
        else:
            rest = suffixes[index + 1][0]
            out.append(f'  {helper}suffix_eq_drop_of_parts\n    {program}.ops {start} {size} {start + size}\n'
                       f'    {chunk} {rest} {suffix}\n    (Eq.refl {start + size}) (Eq.refl {chunk})\n'
                       f'    (Eq.refl ({chunk} ++ {rest})) {rest}_coverage\n\n')
    first = suffixes[0][0]
    coverage = prefix + '_ops_coverage'
    out.append(f'theorem {coverage} : {program}.ops={first} :=\n'
               f'  {helper}ops_eq_suffix_of_drop_zero\n    {program}.ops {first} {first}_coverage\n\n'
               'end LeanVerification.PositiveDCompletion\n')
    old_argument = f'(Eq.refl {first})'
    if guards.count(old_argument) != 1:
        raise ValueError('Expected the one original whole-operation reflexivity argument')
    outputs = dict(phase_files)
    outputs[coverage_name] = ''.join(out)
    outputs[stem + 'Guards'] = f'import {namespace}.{coverage_name}\n' + guards.replace(old_argument, coverage)
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('modules', nargs='+', help='Generated module names without .lean.')
    parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--definitions-directory', type=Path, help='Fallback directory for unchanged analytic definitions; regenerated definitions take precedence.')
    parser.add_argument('--output', type=Path, required=True, help='A separate output directory; checked sources are never overwritten.')
    parser.add_argument('--dag', action='store_true', help='Cache and kernel-check every arithmetic subexpression separately.')
    parser.add_argument('--node-budget', type=int, default=0, help='Inline this many small expression nodes between cached arithmetic checks; 0 caches every node.')
    parser.add_argument('--certificate', action='store_true', help='Emit cached certificate data with one generic Boolean kernel check, without per-node proof tactics.')
    parser.add_argument('--local-checks', action='store_true', help='Share checked child guards using direct constructor-lemma applications.')
    parser.add_argument('--validity', action='store_true', help='Use inductive validity proofs and discard cached arrays before the real-expression bridge.')
    parser.add_argument('--sparse', action='store_true', help='Use sparse integer monomial caches; requires --certificate --validity.')
    parser.add_argument('--program', action='store_true', help='Use one checked sparse instruction stream and two selected outputs.')
    parser.add_argument('--explicit-integers', action='store_true', help='Print sparse-program integer data using Int constructors instead of numeral instances.')
    parser.add_argument('--program-chunk-size', type=int, default=0, help='Split sparse-program data declarations into bounded lists; 0 uses one declaration.')
    parser.add_argument('--literal', action='store_true', help='Decode exact sparse-program data into closed Lean constructors; requires --program.')
    parser.add_argument('--source-value', action='store_true', help='Use the checked numeral-preserving interpreter for a definitional real-expression bridge; requires --program.')
    parser.add_argument('--fast-program', action='store_true', help='Use the separately proved checkFast computation with the same exact program data and source bridge; requires --program.')
    parser.add_argument('--array-program', action='store_true', help='Use the proved balanced-array cache checker with unchanged operations, exact caches, and source bridge; requires --program --literal.')
    parser.add_argument('--array-chunk-size', type=int, default=0, help='Kernel-check this many array-program operations per private guard, then compose all guards with the proved append theorem; requires --array-program. Zero keeps one guard.')
    parser.add_argument('--balanced-array', action='store_true', help='Use the separately proved balanced-product array checker with the same exact certificate data and source-expression bridge; requires --array-program.')
    parser.add_argument('--product-row-chunk-size', type=int, default=0, help='Prove selected large legacy products with this many rows per exact suffix guard, then compose their existing array-operation checks; requires a chunked array program and is incompatible with --balanced-array.')
    parser.add_argument('--product-pair-threshold', type=int, default=4096, help='Use exact product suffix proofs when both operands have at least two terms and their term-pair count reaches this threshold.')
    parser.add_argument('--fast-product-guards', action='store_true', help='Compute bounded suffix guards with the proved equal no-fuel accumulator, retaining the original multiplication/checker statements; requires --product-row-chunk-size.')
    parser.add_argument('--fast-array-guards', action='store_true', help='Compute ordinary operation segments with the proved equal no-fuel checker, retaining every original Array.checkFrom statement; requires a chunked array program and is incompatible with --balanced-array.')
    parser.add_argument('--kernel-decide', action='store_true', help='Use Lean\'s standard decide +kernel tactic for closed Boolean guards, avoiding duplicate elaborator evaluation without native evaluation; requires --program. Erase/source proofs remain unchanged.')
    parser.add_argument('--array-aliases', action='store_true', help='Transport explicit operation-list and next-index equalities when composing original array guards; requires a chunked array program and is incompatible with --balanced-array.')
    parser.add_argument('--split-kernel', action='store_true', help='Emit a generic-only ModuleKernel.lean with the checked SourceValue identity and retain the exact original theorem in a small importing wrapper; requires --program --source-value.')
    parser.add_argument('--split-kernel-phases', action='store_true', help='Separate a selected exact Kernel into shared Program/Plain Data, independent Guards and Erase modules, and a generic composition theorem; requires --split-kernel and the original array checker.')
    parser.add_argument('--guard-theorems-per-module', type=int, default=0, help='Move unchanged guard data into one shared module and bound the number of intermediate guard theorem declarations per dependency-ordered module; requires --split-kernel-phases. Zero keeps one Guards file.')
    parser.add_argument('--array-coverage', action='store_true', help='Prove complete original operation coverage from unchanged drop/take slices, avoiding one global list conversion; requires explicit aliases, bounded phase files and kernel decision guards.')
    args = parser.parse_args()
    if args.sparse and not (args.certificate and args.validity):
        parser.error('--sparse requires --certificate --validity')
    if (args.literal or args.source_value or args.fast_program) and not args.program:
        parser.error('--literal, --source-value, and --fast-program require --program')
    if args.array_program and (not args.program or not args.literal or args.fast_program or args.program_chunk_size):
        parser.error('--array-program requires --program --literal and is incompatible with --fast-program and --program-chunk-size')
    if args.array_chunk_size < 0 or (args.array_chunk_size and not args.array_program):
        parser.error('--array-chunk-size must be nonnegative and requires --array-program')
    if args.balanced_array and not args.array_program:
        parser.error('--balanced-array requires --array-program')
    if args.product_row_chunk_size < 0 or (args.product_row_chunk_size and
            (not args.array_program or not args.array_chunk_size or args.balanced_array)):
        parser.error('--product-row-chunk-size must be nonnegative, requires --array-program --array-chunk-size, and is incompatible with --balanced-array')
    if args.product_pair_threshold < 1:
        parser.error('--product-pair-threshold must be positive')
    if args.fast_product_guards and not args.product_row_chunk_size:
        parser.error('--fast-product-guards requires --product-row-chunk-size')
    if args.fast_array_guards and (not args.array_program or not args.array_chunk_size or args.balanced_array):
        parser.error('--fast-array-guards requires --array-program --array-chunk-size and is incompatible with --balanced-array')
    if args.kernel_decide and not args.program:
        parser.error('--kernel-decide requires --program')
    if args.array_aliases and (not args.array_program or not args.array_chunk_size or args.balanced_array):
        parser.error('--array-aliases requires --array-program --array-chunk-size and is incompatible with --balanced-array')
    if args.split_kernel and not (args.program and args.source_value):
        parser.error('--split-kernel requires --program --source-value')
    if args.split_kernel_phases and (not args.split_kernel or not args.array_program or args.balanced_array):
        parser.error('--split-kernel-phases requires --split-kernel --array-program and retains the original array checker')
    if args.guard_theorems_per_module < 0 or (args.guard_theorems_per_module and not args.split_kernel_phases):
        parser.error('--guard-theorems-per-module must be nonnegative and requires --split-kernel-phases')
    if args.array_coverage and not (args.array_aliases and args.guard_theorems_per_module and args.kernel_decide):
        parser.error('--array-coverage requires --array-aliases --guard-theorems-per-module --kernel-decide')
    source = args.directory.resolve()
    output = args.output.resolve()
    if source == output:
        parser.error('Use a separate output directory and review the generated changes.')
    output.mkdir(parents=True, exist_ok=True)
    definitions = Definitions(source, args.definitions_directory.resolve() if args.definitions_directory else None)
    for module in args.modules:
        kernel_module = f'LeanVerification.PositiveDCompletion.{module}Kernel' if args.split_kernel else None
        text, count, kernel_text = compact((source / (module + '.lean')).read_text(), definitions, dag=args.dag, node_budget=args.node_budget, certificate=args.certificate,local_checks=args.local_checks,validity=args.validity,sparse=args.sparse,program=args.program,explicit_integers=args.explicit_integers,program_chunk_size=args.program_chunk_size,literal=args.literal,source_value=args.source_value,fast_program=args.fast_program,array_program=args.array_program,array_chunk_size=args.array_chunk_size,split_kernel_module=kernel_module,balanced_array=args.balanced_array,product_row_chunk_size=args.product_row_chunk_size,product_pair_threshold=args.product_pair_threshold,fast_product_guards=args.fast_product_guards,fast_array_guards=args.fast_array_guards,kernel_decide=args.kernel_decide,array_aliases=args.array_aliases)
        if count == 0:
            raise ValueError(f'No eligible identities in {module}')
        destination = output / (module + '.lean')
        destination.write_text(text)
        print(f'{module}: {count} kernel coefficient checks; {destination.stat().st_size} source bytes')
        if kernel_text is not None:
            kernel_files = (split_kernel_phases(kernel_text, kernel_module) if args.split_kernel_phases
                            else {module + 'Kernel': kernel_text})
            if args.guard_theorems_per_module:
                kernel_files = split_guard_units(kernel_files, kernel_module, args.guard_theorems_per_module)
            if args.array_coverage:
                kernel_files = add_array_coverage(kernel_files, kernel_module)
            for kernel_name, contents in kernel_files.items():
                kernel_destination = output / (kernel_name + '.lean')
                kernel_destination.write_text(contents)
                print(f'{kernel_name}: {kernel_destination.stat().st_size} source bytes')


if __name__ == '__main__':
    main()
