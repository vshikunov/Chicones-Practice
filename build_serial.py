#!/usr/bin/env python3
"""Build the positive-D proof closure with one Lake target process at a time.

Run this prebuild before an unrestricted aggregate build on a small-memory
machine.  The dependency order prevents Lake from starting several large new
certificate modules concurrently.  Existing valid Lake artifacts are reused.
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path


PREFIX = 'LeanVerification.PositiveDCompletion.'


def ordered_modules(source):
    files = {p.stem: p for p in source.glob('*.lean')}
    visited, active, order = set(), set(), []

    def visit(name):
        if name in visited:
            return
        if name in active:
            raise ValueError(f'Import cycle at {name}')
        active.add(name)
        text = files[name].read_text()
        for dependency in re.findall(r'^import LeanVerification\.PositiveDCompletion\.(\w+)', text, re.M):
            visit(dependency)
        active.remove(name)
        visited.add(name)
        order.append(name)

    visit('CompleteRow2')
    unused = set(files) - visited
    if unused:
        raise ValueError(f'Unreachable proof modules: {sorted(unused)}')
    return order


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin-dir', type=Path, help='Directory containing the Lean 4.19.0 lake and lean executables.')
    parser.add_argument('--logs-dir', type=Path, help='Per-target log directory; default: logs/positive_d_serial.')
    parser.add_argument('--list', action='store_true', help='Print the dependency order without running Lean or Lake.')
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    project = source.parents[1]
    names = ordered_modules(source)
    if args.list:
        print('\n'.join(PREFIX + name for name in names))
        return
    env = os.environ.copy()
    if args.lean_bin_dir:
        directory = args.lean_bin_dir.resolve()
        lake = directory / ('lake.exe' if os.name == 'nt' else 'lake')
        if not lake.is_file():
            parser.error(f'Lake executable not found: {lake}')
        env['PATH'] = str(directory) + os.pathsep + env.get('PATH', '')
        lake_command = str(lake)
    else:
        lake_command = shutil.which('lake')
        if lake_command is None:
            parser.error('Lake is not on PATH; supply --lean-bin-dir.')
    logs = args.logs_dir.resolve() if args.logs_dir else project / 'logs/positive_d_serial'
    logs.mkdir(parents=True, exist_ok=True)
    manifest = logs / 'results.jsonl'
    for index, name in enumerate(names, 1):
        target = PREFIX + name
        command = [lake_command, 'build', target]
        digest = hashlib.sha256((source / (name + '.lean')).read_bytes()).hexdigest()
        print(f'[{index}/{len(names)}] {target}', flush=True)
        start = time.monotonic()
        with (logs / (name + '.log')).open('w') as log:
            result = subprocess.run(command, cwd=project, env=env, stdout=log, stderr=subprocess.STDOUT)
        record = {'target': target, 'source_sha256': digest,
                  'returncode': result.returncode, 'seconds': round(time.monotonic()-start, 3)}
        with manifest.open('a') as output:
            output.write(json.dumps(record, sort_keys=True) + '\n')
        if result.returncode:
            print(f'Build failed: {target}; see {logs / (name + ".log")}', file=sys.stderr)
            raise SystemExit(result.returncode)
    print(f'All {len(names)} positive-D modules built successfully.', flush=True)


if __name__ == '__main__':
    main()
