#!/usr/bin/env python3
"""Reproduce every generated positive-D proof module without modifying checked sources."""
import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Keep regenerated sources in this directory.')
    parser.add_argument('--check', action='store_true', help='Fail if a generated module differs from its checked source.')
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    temporary = tempfile.TemporaryDirectory(prefix='positive_d_reproduction_') if args.output is None else None
    output = Path(temporary.name) if temporary else args.output.resolve()
    if output == source:
        parser.error('The output must be separate from the checked source directory.')
    output.mkdir(parents=True, exist_ok=True)
    def run(script, *arguments):
        subprocess.run([sys.executable, str(source / script), *map(str, arguments)], check=True)
    for generator in ['generate_upper_certificates.py', 'generate_correlated_upper_certificates.py',
                      'generate_lower_certificates.py', 'generate_lower_maps.py',
                      'generate_leaf_wrappers.py', 'generate_source_coefficients.py',
                      'generate_pole_coefficients.py', 'generate_rho_pole_partition.py']:
        run(generator, '--output', output)
    names = [f'UpperPolynomial{i:02d}' for i in (8, 9)]
    names += [f'UpperCertificate{i:02d}' for i in (7, 8, 9)]
    names += [name for i in range(10) for name in (f'LowerPolynomial{i:02d}', f'LowerCertificate{i:02d}')]
    run('partition_certificates.py', '--directory', output, *names)
    # The compact proofs preserve these generated theorem statements. Rebuild
    # them from the raw polynomial identities, rather than compacting an
    # already compacted source or treating cached certificate data as an oracle.
    manifest_path = source / 'compact_generation_manifest.json'
    if manifest_path.exists():
        manifest = json.loads(manifest_path.read_text())
        if manifest.get('format_version') != 1:
            raise ValueError('Unsupported compact-generation manifest version')
        modules = manifest['modules']
        if len(modules) != len(set(modules)) or not modules:
            raise ValueError('Compact-generation modules must be distinct and nonempty')
        if manifest['arguments'] != ['--program', '--literal', '--source-value']:
            raise ValueError('Unexpected compact-generation arguments')
        array_modules = manifest.get('array_modules', [])
        if len(array_modules) != len(set(array_modules)) or not set(array_modules) <= set(modules):
            raise ValueError('Array-checker modules must be a distinct subset of compact modules')
        chunk_modules = manifest.get('array_chunk_modules', [])
        chunk_size = manifest.get('array_chunk_size', 0)
        if len(chunk_modules) != len(set(chunk_modules)) or not set(chunk_modules) <= set(array_modules):
            raise ValueError('Chunked array modules must be a distinct subset of array modules')
        if not isinstance(chunk_size, int) or chunk_size < 0 or (chunk_modules and chunk_size == 0):
            raise ValueError('Chunked array modules need a positive integer chunk size')
        split_modules = manifest.get('split_kernel_modules', [])
        if len(split_modules) != len(set(split_modules)) or not set(split_modules) <= set(modules):
            raise ValueError('Split-kernel modules must be a distinct subset of compact modules')
        balanced_modules = manifest.get('balanced_array_modules', [])
        if len(balanced_modules) != len(set(balanced_modules)) or not set(balanced_modules) <= set(array_modules):
            raise ValueError('Balanced-product modules must be a distinct subset of array modules')
        product_modules = manifest.get('product_row_modules', [])
        product_chunk_size = manifest.get('product_row_chunk_size', 0)
        product_threshold = manifest.get('product_pair_threshold', 4096)
        if len(product_modules) != len(set(product_modules)) or not set(product_modules) <= set(chunk_modules):
            raise ValueError('Product-row modules must be a distinct subset of chunked array modules')
        if set(product_modules) & set(balanced_modules):
            raise ValueError('Product-row modules retain the original array checker')
        if not isinstance(product_chunk_size, int) or product_chunk_size < 0 or (product_modules and product_chunk_size == 0):
            raise ValueError('Product-row modules need a positive integer row chunk size')
        if not isinstance(product_threshold, int) or product_threshold < 1:
            raise ValueError('The product term-pair threshold must be a positive integer')
        fast_product_modules = manifest.get('fast_product_modules', [])
        if len(fast_product_modules) != len(set(fast_product_modules)) or not set(fast_product_modules) <= set(product_modules):
            raise ValueError('Fast product guards must be a distinct subset of product-row modules')
        fast_array_modules = manifest.get('fast_array_modules', [])
        if len(fast_array_modules) != len(set(fast_array_modules)) or not set(fast_array_modules) <= set(chunk_modules):
            raise ValueError('Fast array guards must be a distinct subset of chunked array modules')
        if set(fast_array_modules) & set(balanced_modules):
            raise ValueError('Fast array guards retain the original array checker')
        kernel_decide_modules = manifest.get('kernel_decide_modules', [])
        if len(kernel_decide_modules) != len(set(kernel_decide_modules)) or not set(kernel_decide_modules) <= set(modules):
            raise ValueError('Kernel-decision modules must be a distinct subset of compact modules')
        alias_modules = manifest.get('array_alias_modules', [])
        if len(alias_modules) != len(set(alias_modules)) or not set(alias_modules) <= set(chunk_modules):
            raise ValueError('Explicit array aliases must be a distinct subset of chunked array modules')
        if set(alias_modules) & set(balanced_modules):
            raise ValueError('Explicit array aliases retain the original array checker')
        phase_modules = manifest.get('split_kernel_phase_modules', [])
        if (len(phase_modules) != len(set(phase_modules)) or
                not set(phase_modules) <= set(split_modules) & set(array_modules)):
            raise ValueError('Phase-split kernels must be a distinct subset of split original-array modules')
        if set(phase_modules) & set(balanced_modules):
            raise ValueError('Phase-split kernels retain the original array checker')
        guard_unit_modules = manifest.get('guard_unit_modules', [])
        guard_bound = manifest.get('guard_theorems_per_module', 0)
        if len(guard_unit_modules) != len(set(guard_unit_modules)) or not set(guard_unit_modules) <= set(phase_modules):
            raise ValueError('Guard-unit modules must be a distinct subset of phase-split modules')
        if not isinstance(guard_bound, int) or guard_bound < 0 or (guard_unit_modules and guard_bound == 0):
            raise ValueError('Guard units need a positive integer theorem bound')
        coverage_modules = manifest.get('array_coverage_modules', [])
        if (len(coverage_modules) != len(set(coverage_modules)) or
                not set(coverage_modules) <= (set(guard_unit_modules) & set(alias_modules) & set(kernel_decide_modules))):
            raise ValueError('Coverage modules must be a distinct subset of bounded, explicitly aliased kernel-decision modules')
        data_group_modules = manifest.get('data_group_modules', [])
        data_group_bound = manifest.get('data_groups_per_module', 0)
        if (len(data_group_modules) != len(set(data_group_modules)) or
                not set(data_group_modules) <= {f'LowerCertificate{i:02d}' for i in range(6, 10)}):
            raise ValueError('Data-group modules must be a distinct selected subset of unaccepted leaves06–09')
        if not isinstance(data_group_bound, int) or data_group_bound < 0 or (data_group_modules and data_group_bound == 0):
            raise ValueError('Data partitions need a positive group bound')
        # Selected correlated certificates need only coordinate definitions in
        # their Data modules. Keep the complete coordinate proofs explicitly
        # imported by their final aggregates, preserving the physical chain.
        for certificate in manifest.get('data_only_dependencies', []):
            if certificate not in ('UpperCertificate08', 'UpperCertificate09'):
                raise ValueError(f'Unsupported selected Data dependency: {certificate}')
            polynomial = certificate.replace('Certificate', 'Polynomial')
            data_path = output / (certificate + 'Data.lean')
            aggregate_path = output / (certificate + '.lean')
            full_import = f'import LeanVerification.PositiveDCompletion.{polynomial}\n'
            data_import = f'import LeanVerification.PositiveDCompletion.{polynomial}Data\n'
            data_text = data_path.read_text()
            if data_text.count(full_import) != 1:
                raise ValueError(f'Expected one coordinate import in {data_path.name}')
            data_path.write_text(data_text.replace(full_import, data_import))
            aggregate_path.write_text(full_import + aggregate_path.read_text())
        for module in modules:
            if not (output / (module + '.lean')).is_file():
                raise ValueError(f'Missing raw generated module: {module}')
        with tempfile.TemporaryDirectory(prefix='positive_d_compact_reproduction_') as compact_dir:
            compact_output = Path(compact_dir)
            groups = {}
            for module in modules:
                mode = (module in array_modules, module in chunk_modules,
                        module in split_modules, module in balanced_modules,
                        module in product_modules, module in fast_product_modules,
                        module in fast_array_modules, module in kernel_decide_modules,
                        module in alias_modules, module in phase_modules, module in guard_unit_modules, module in coverage_modules)
                groups.setdefault(mode, []).append(module)
            for (array_mode, chunk_mode, split_mode, balanced_mode, product_mode, fast_product_mode, fast_array_mode, kernel_decide_mode, alias_mode, phase_mode, guard_unit_mode, coverage_mode), selected in sorted(groups.items()):
                extra = ['--array-program'] if array_mode else []
                if chunk_mode:
                    extra += ['--array-chunk-size', str(chunk_size)]
                if split_mode:
                    extra += ['--split-kernel']
                if balanced_mode:
                    extra += ['--balanced-array']
                if product_mode:
                    extra += ['--product-row-chunk-size', str(product_chunk_size),
                              '--product-pair-threshold', str(product_threshold)]
                if fast_product_mode:
                    extra += ['--fast-product-guards']
                if fast_array_mode:
                    extra += ['--fast-array-guards']
                if kernel_decide_mode:
                    extra += ['--kernel-decide']
                if alias_mode:
                    extra += ['--array-aliases']
                if phase_mode:
                    extra += ['--split-kernel-phases']
                if guard_unit_mode:
                    extra += ['--guard-theorems-per-module', str(guard_bound)]
                if coverage_mode:
                    extra += ['--array-coverage']
                run('compact_polynomial_identities.py', *selected,
                    '--directory', output, '--definitions-directory', source,
                    '--output', compact_output, *manifest['arguments'], *extra)
            generated_modules = modules + [module + 'Kernel' for module in split_modules]
            generated_modules += [module + 'Kernel' + part for module in phase_modules
                                  for part in ('Data', 'Guards', 'Erase')]
            for module in guard_unit_modules:
                data_name = module + 'KernelGuardData'
                proof_names = sorted(path.stem for path in compact_output.glob(module + 'KernelGuardProof*.lean'))
                if proof_names != [module + f'KernelGuardProof{i:04d}' for i in range(len(proof_names))] or not proof_names:
                    raise ValueError(f'Unexpected guard proof-unit sequence for {module}')
                if not (compact_output / (data_name + '.lean')).is_file():
                    raise ValueError(f'Missing shared guard data for {module}')
                generated_modules += [data_name] + proof_names
            generated_modules += [module + 'KernelCoverage' for module in coverage_modules]
            for module in generated_modules:
                shutil.copyfile(compact_output / (module + '.lean'),
                                output / (module + '.lean'))
        if data_group_modules:
            with tempfile.TemporaryDirectory(prefix='positive_d_data_partition_') as data_dir:
                data_output = Path(data_dir)
                run('partition_data_groups.py', *data_group_modules,
                    '--directory', output, '--output', data_output,
                    '--groups-per-module', str(data_group_bound))
                for module in data_group_modules:
                    helpers = sorted(path.stem for path in data_output.glob(module + 'DataPart*.lean'))
                    if helpers != [module + f'DataPart{i:02d}' for i in range(len(helpers))] or not helpers:
                        raise ValueError(f'Unexpected Data part sequence for {module}')
                    for name in helpers + [module + 'Data']:
                        shutil.copyfile(data_output / (name + '.lean'), output / (name + '.lean'))
    files = sorted(output.glob('*.lean'))
    differences = [p.name for p in files if not (source / p.name).is_file() or p.read_bytes() != (source / p.name).read_bytes()]
    report = {'generated_modules': len(files), 'differences': differences}
    print(json.dumps(report, indent=2))
    if args.check and differences:
        raise SystemExit(1)
    if temporary:
        temporary.cleanup()


if __name__ == '__main__':
    main()
