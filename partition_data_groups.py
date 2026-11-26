#!/usr/bin/env python3
"""Partition existing generated certificate data without changing declarations."""
import argparse
from pathlib import Path
import re


def partition_data(text, module, groups_per_module):
    if not re.fullmatch(r'LowerCertificate\d{2}', module) or groups_per_module < 1:
        raise ValueError('Expected a generated lower certificate and positive group bound')
    stem = module + 'Data'
    prefix = module[0].lower() + module[1:]
    declaration = re.compile(r'^(?:noncomputable )?(def|theorem) (\w+)\b', re.M)
    matches = list(declaration.finditer(text))
    ending = 'end LeanVerification.PositiveDCompletion\n'
    if not matches or not text.endswith(ending):
        raise ValueError('Unexpected generated Data module shape')
    records = [(m[2], m[1], text[m.start():matches[i+1].start()
                if i+1 < len(matches) else len(text)-len(ending)])
               for i, m in enumerate(matches)]
    names = {name for name, kind, body in records}
    if len(names) != len(records) or records[-1][0] != prefix:
        raise ValueError('Expected unique declarations ending with the original certificate definition')
    group_ids = []
    groups = {}
    for name, kind, body in records[:-1]:
        match = re.fullmatch(re.escape(prefix) + r'(?:Weight(\d{2})(?:_pos)?|Block(\d{2})(?:Coeff\d+)?)', name)
        if match is None:
            raise ValueError(f'Unexpected declaration outside a Weight/Block group: {name}')
        group = int(match[1] or match[2])
        groups.setdefault(group, []).append((name, kind, body))
        if not group_ids or group_ids[-1] != group:
            group_ids.append(group)
    if group_ids != list(range(len(group_ids))) or set(groups) != set(group_ids):
        raise ValueError('Weight/Block groups must be consecutive and noninterleaved')
    for group, declarations in groups.items():
        required = [prefix + f'Weight{group:02d}', prefix + f'Weight{group:02d}_pos', prefix + f'Block{group:02d}']
        if [name for name, kind, body in declarations[:3]] != required:
            raise ValueError(f'Missing original Weight/positivity/Block prefix in group{group:02d}')
        coeffs = [name for name, kind, body in declarations[3:]]
        if coeffs != [prefix + f'Block{group:02d}Coeff{i}' for i in range(len(coeffs))] or not coeffs:
            raise ValueError(f'Coefficient declarations are not consecutive in group{group:02d}')
    part_names = [stem + f'Part{i:02d}' for i in range((len(groups)+groups_per_module-1)//groups_per_module)]
    owner = {name: part_names[group // groups_per_module]
             for group, declarations in groups.items() for name, kind, body in declarations}
    owner[prefix] = stem
    references = {name: (set(re.findall(r'\b[A-Za-z_][A-Za-z_0-9]*\b', body)) & names) - {name}
                  for name, kind, body in records}
    order = {name: i for i, (name, kind, body) in enumerate(records)}
    for name, dependencies in references.items():
        if any(order[dependency] >= order[name] for dependency in dependencies):
            raise ValueError(f'Unexpected forward Data reference in {name}')
    header = text[:matches[0].start()]
    output = {}
    for target in part_names + [stem]:
        selected = [(name, body) for name, kind, body in records if owner[name] == target]
        dependencies = sorted({owner[dependency] for name, body in selected
                               for dependency in references[name] if owner[dependency] != target})
        imports = ''.join(f'import LeanVerification.PositiveDCompletion.{dependency}\n' for dependency in dependencies)
        output[target] = imports + header + ''.join(body for name, body in selected) + ending
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('modules', nargs='+')
    parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--groups-per-module', type=int, default=5)
    args = parser.parse_args()
    source, output = args.directory.resolve(), args.output.resolve()
    if source == output:
        parser.error('Use a separate output directory for reviewable Data partitions')
    output.mkdir(parents=True, exist_ok=True)
    for module in args.modules:
        parts = partition_data((source / (module + 'Data.lean')).read_text(), module, args.groups_per_module)
        for name, text in parts.items():
            path = output / (name + '.lean')
            path.write_text(text)
            print(f'{name}: {path.stat().st_size} source bytes')


if __name__ == '__main__':
    main()
