#!/usr/bin/env python3
"""Record a Lake build, optionally instrumenting compiler children without replacing Lean.

POSIX only. Clean runs move the old project build tree into the result directory.
No dependency caches or installed toolchains are modified. Existing labels are rejected.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys
import time

TARGETS = ['ToMathlib', 'VCVio', 'LatticeCrypto', 'Extern', 'HashSig', 'Examples', 'VCVioWidgets']


def now():
    # Python 3.9 on macOS uses a process-relative epoch for time.monotonic().
    # clock_gettime has a system-wide epoch, needed to correlate child processes.
    return time.clock_gettime(time.CLOCK_MONOTONIC)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compiler():
    """Entry point when invoked through the temporary bin/lean or bin/clang link."""
    kind = Path(sys.argv[0]).name
    real = Path(os.environ['VCVIO_PERF_REAL_ROOT']) / 'bin' / kind
    args = sys.argv[1:]
    out = Path(os.environ['VCVIO_PERF_RECORDS'])
    module = None
    source = next((a for a in args if a.endswith('.lean')), None)
    if '--setup' in args:
        setup = Path(args[args.index('--setup') + 1])
        module = json.loads(setup.read_text())['name']
    has_message_guards = bool(source and '#guard_msgs' in Path(source).read_text())
    if kind == 'lean' and module:
        # Profiler info messages change #guard_msgs expectations. Keep these
        # modules fully checked, but do not inject profiler messages into them.
        if os.environ.get('VCVIO_PERF_PROFILE') == '1' and not has_message_guards:
            args += ['--profile', '-Dprofiler.threshold=10']
        if os.environ.get('VCVIO_PERF_THREADS'):
            args += ['-j' + os.environ['VCVIO_PERF_THREADS']]
    start = now()
    p = subprocess.Popen([str(real), *args])
    (out / f'{os.getpid()}.start.json').write_text(json.dumps(dict(
        kind=kind, module=module, pid=p.pid, start=start)) + '\n')
    def forward(signum, _frame):
        if p.returncode is None:
            p.send_signal(signum)
    signal.signal(signal.SIGTERM, forward)
    signal.signal(signal.SIGINT, forward)
    _, status, usage = os.wait4(p.pid, 0)
    p.returncode = os.waitstatus_to_exitcode(status)
    end = now()
    artifacts = {}
    for flag in ['-o', '-i', '-c']:
        if flag in args and args.index(flag) + 1 < len(args):
            path = Path(args[args.index(flag) + 1])
            if path.is_file():
                artifacts[str(path)] = path.stat().st_size
            if flag == '-o' and path.suffix == '.olean':
                for suffix in ['.olean.server', '.olean.private', '.ir', '.ir.sig']:
                    extra = path.with_suffix(suffix)
                    if extra.is_file():
                        artifacts[str(extra)] = extra.stat().st_size
    record = dict(kind=kind, module=module, source=source, pid=p.pid,
                  profile_skipped_for_message_guards=has_message_guards,
                  start=start, end=end, wall_seconds=end-start,
                  user_seconds=usage.ru_utime, system_seconds=usage.ru_stime,
                  peak_rss_bytes=usage.ru_maxrss * (1 if sys.platform == 'darwin' else 1024),
                  voluntary_switches=usage.ru_nvcsw, involuntary_switches=usage.ru_nivcsw,
                  exit_code=p.returncode, command=[str(real), *args], artifacts=artifacts)
    if source and Path(source).is_file():
        record['source_sha256'] = sha(Path(source))
    (out / f'{os.getpid()}-{time.monotonic_ns()}.json').write_text(json.dumps(record) + '\n')
    return p.returncode if p.returncode >= 0 else 128 - p.returncode


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--label', required=True)
    parser.add_argument('--clean', action='store_true')
    parser.add_argument('--instrument', action='store_true')
    parser.add_argument('--profile', action='store_true')
    parser.add_argument('--threads', type=int)
    parser.add_argument('--lake-config', action='append', default=[],
                        help='explicit Lake -K configuration, recorded in provenance')
    parser.add_argument('--timeout', type=float, default=900)
    args = parser.parse_args()
    if args.timeout <= 0 or (args.threads is not None and args.threads < 1):
        parser.error('timeout and thread count must be positive')
    if (args.profile or args.threads is not None) and not args.instrument:
        parser.error('--profile and --threads require --instrument')
    if not hasattr(os, 'wait4'):
        parser.error('requires POSIX os.wait4')
    root = args.root.resolve()
    output = args.output.resolve() / args.label
    if (root / '.lake/build') in output.parents:
        parser.error('output must be outside the project build directory')
    if output.exists():
        parser.error('label already exists')
    output.mkdir(parents=True)
    records = output / 'processes'
    records.mkdir()
    real = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=root, text=True).strip())
    env = os.environ.copy()
    if args.instrument:
        view = output / 'toolchain'
        view.mkdir()
        (view / 'bin').mkdir()
        for entry in real.iterdir():
            if entry.name != 'bin':
                (view / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
        for entry in (real / 'bin').iterdir():
            target = Path(__file__).resolve() if entry.name in ['lean', 'clang', 'leanc'] else entry
            (view / 'bin' / entry.name).symlink_to(target)
        env.update(LAKE_OVERRIDE_LEAN='true', LEAN_SYSROOT=str(view),
                   VCVIO_PERF_REAL_ROOT=str(real), VCVIO_PERF_RECORDS=str(records),
                   VCVIO_PERF_PROFILE='1' if args.profile else '0',
                   VCVIO_PERF_THREADS=str(args.threads) if args.threads else '')
    build = root / '.lake/build'
    if args.clean and build.exists():
        build.rename(output / 'saved-project-build')
    command = ['lake', *['-K' + value for value in args.lake_config], 'build', *TARGETS]
    provenance = dict(root=str(root), command=command, targets=TARGETS,
                      commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
                      diff=subprocess.check_output(['git', 'diff'], cwd=root, text=True),
                      platform=platform.platform(), logical_cpus=os.cpu_count(),
                      thread_environment={key: env.get(key) for key in
                          ['LEAN_NUM_THREADS', 'LEAN_MAIN_USE_THREAD', 'OMP_NUM_THREADS']},
                      toolchain=(root / 'lean-toolchain').read_text().strip(),
                      started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                      manifest_sha256=sha(root / 'lake-manifest.json'),
                      source_sha256={path: sha(root / path) for path in
                          subprocess.check_output(
                              ['git', 'ls-files', '--cached', '--others',
                               '--exclude-standard', '--', '*.lean'],
                              cwd=root, text=True).splitlines()
                          if (root / path).is_file()},
                      clean=args.clean, instrument=args.instrument, profile=args.profile,
                      threads=args.threads)
    (output / 'provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
    start = now()
    samples = []
    with (output / 'build.log').open('wb') as log:
        p = subprocess.Popen(command, cwd=root, env=env, stdout=log, stderr=log,
                             start_new_session=True)
        timed_out = False
        while True:
            pid, status, usage = os.wait4(p.pid, os.WNOHANG)
            if pid:
                break
            if now() - start > args.timeout:
                timed_out = True
                os.killpg(p.pid, signal.SIGKILL)
                _, status, usage = os.wait4(p.pid, 0)
                break
            samples.append(dict(time=now(), load_average=os.getloadavg()))
            time.sleep(0.1)
        p.returncode = os.waitstatus_to_exitcode(status)
    result = dict(start=start, end=now(), wall_seconds=now()-start,
                  user_seconds=usage.ru_utime, system_seconds=usage.ru_stime,
                  exit_code=p.returncode, timed_out=timed_out)
    (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    (output / 'load.json').write_text(json.dumps(samples) + '\n')
    print(json.dumps(dict(label=args.label, **result)), flush=True)
    if p.returncode:
        print((output / 'build.log').read_text(errors='replace')[-8000:], file=sys.stderr)
    return p.returncode if p.returncode >= 0 else 128 - p.returncode


if __name__ == '__main__':
    sys.exit(compiler() if Path(sys.argv[0]).name in ['lean', 'clang', 'leanc'] else main())
