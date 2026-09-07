#!/usr/bin/env python3
"""Analyze profile_build.py child records and Lean's direct-import metadata."""

import argparse
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path


def analyze(run, build):
    result = json.loads((run / 'result.json').read_text())
    if result['exit_code'] != 0:
        raise ValueError('failed builds are diagnostics, not comparable build profiles')
    records = [json.loads(p.read_text()) for p in (run / 'processes').glob('*.json')
               if not p.name.endswith('.start.json')]
    modules = {r['module']: r for r in records if r['kind'] == 'lean' and r['module']}
    if len(modules) != sum(r['kind'] == 'lean' and bool(r['module']) for r in records):
        raise ValueError('duplicate module compilations require separate runs')
    if not modules:
        raise ValueError('no compiler modules recorded; a cache hit is not a compile profile')
    if any(r['exit_code'] != 0 for r in records):
        raise ValueError('failed compiler processes are not comparable build profiles')
    graph = {}
    for name, record in modules.items():
        path = build / 'lib/lean' / Path(*name.split('.')).with_suffix('.ilean')
        if not path.exists():
            raise ValueError(f'missing import metadata for {name}: {path}')
        data = json.loads(path.read_text())
        if not all(isinstance(i, list) and len(i) == 4 and isinstance(i[0], str)
                   for i in data['directImports']):
            raise ValueError(f'unsupported directImports schema for {name}')
        graph[name] = [i[0] for i in data['directImports'] if i[0] in modules]
        record['imports'] = data['directImports']
        record['ready'] = max((modules[i]['end'] for i in graph[name]), default=result['start'])
        record['launch_gap_seconds'] = record['start'] - record['ready']
        if record['launch_gap_seconds'] < -0.1:
            raise ValueError(f'inconsistent timestamps or imports for {name}')

    @lru_cache(None)
    def weighted(name):
        previous = max((weighted(i) for i in graph[name]), default=(0, []), key=lambda p: p[0])
        return previous[0] + modules[name]['wall_seconds'], previous[1] + [name]

    @lru_cache(None)
    def ancestors(name):
        return frozenset(graph[name]) | frozenset(a for i in graph[name] for a in ancestors(i))

    last = max(modules, key=lambda n: modules[n]['end'])
    observed = [last]
    while graph[observed[-1]]:
        observed.append(max(graph[observed[-1]], key=lambda n: modules[n]['end']))
    observed.reverse()
    longest = max((weighted(n) for n in modules), key=lambda p: p[0])
    events = sorted([(r['start'], 1) for r in modules.values()] +
                    [(r['end'], -1) for r in modules.values()])
    active = peak = 0
    occupancy = Counter()
    previous = result['start']
    for t, delta in events:
        occupancy[active] += t-previous
        active += delta
        peak = max(peak, active)
        previous = t
    occupancy[active] += result['end']-previous
    module_cpu = sum(r['user_seconds'] + r['system_seconds'] for r in modules.values())
    total_cpu = result['user_seconds'] + result['system_seconds']
    ranked = lambda key: sorted(modules, key=lambda n: key(modules[n]), reverse=True)
    rows = [{**r, 'descendants': sum(n in ancestors(m) for m in modules)} for n, r in modules.items()]
    return dict(result=result, module_count=len(modules), module_cpu_seconds=module_cpu,
                residual_cpu_seconds=total_cpu-module_cpu, peak_compilers=peak,
                compiler_occupancy_seconds=dict(occupancy), weighted_path=longest,
                observed_terminal_path=observed,
                rankings=dict(cpu=ranked(lambda r: r['user_seconds']+r['system_seconds']),
                              duration=ranked(lambda r: r['wall_seconds']),
                              launch_gap=ranked(lambda r: r['launch_gap_seconds'])),
                modules=rows)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('run', type=Path)
    p.add_argument('--build-dir', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    if args.output.exists():
        p.error('output already exists')
    data = analyze(args.run, args.build_dir)
    args.output.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({k: data[k] for k in ['module_count', 'module_cpu_seconds',
                     'residual_cpu_seconds', 'peak_compilers', 'weighted_path',
                     'observed_terminal_path']}, indent=2))


if __name__ == '__main__':
    main()
