#!/usr/bin/env python3
"""Replay a built Lean module with its Lake setup and record isolated measurements.

Build the module first. Outputs and logs go to --output, never to Lake's build tree.
Run without profiler options for comparable timings; instrumentation is diagnostic.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import subprocess
import sys
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module")
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--label", default="baseline")
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument("--warmup", type=int, default=1)
    parser.add_argument("--source", type=Path)
    parser.add_argument("--option", action="append", default=[])
    parser.add_argument("--plugin", type=Path, action="append", default=[],
                        help="load a pre-built native Lean plugin (repeatable)")
    parser.add_argument("--profile", action="store_true")
    parser.add_argument("--trace", action="store_true")
    parser.add_argument("--sample", action="store_true",
                        help="collect a macOS sample of the actual Lean child process")
    parser.add_argument("--timeout", type=float, default=300,
                        help="maximum seconds per invocation (default: 300)")
    args = parser.parse_args()
    if args.runs < 1 or args.warmup < 0 or args.timeout <= 0:
        parser.error("runs and timeout must be positive and warmup nonnegative")
    if args.sample and (sys.platform != "darwin" or not Path("/usr/bin/sample").exists()):
        parser.error("--sample requires macOS /usr/bin/sample")
    if not hasattr(os, "wait4"):
        parser.error("this runner requires a POSIX platform with os.wait4")
    root = args.root.resolve()
    plugins = [path.resolve() for path in args.plugin]
    if any(not path.is_file() for path in plugins):
        parser.error("every --plugin must name an existing built library")
    relative = Path(*args.module.split("."))
    source = (args.source or root / relative.with_suffix(".lean")).resolve()
    setup = root / ".lake/build/ir" / relative.with_suffix(".setup.json")
    trace = root / ".lake/build/lib/lean" / relative.with_suffix(".trace")
    # Use the actual recorded invocation to preserve plugins, setup, and output facets.
    entries = json.loads(trace.read_text())["log"]
    invocation = next(e["message"][3:] for e in entries
                      if e["message"].startswith(".> ") and " --setup " in e["message"])
    words = shlex.split(invocation)
    env = os.environ.copy()
    while words and "=" in words[0] and not words[0].startswith("-"):
        key, value = words.pop(0).split("=", 1)
        env[key] = value
    binary = Path(words[0])
    installed = subprocess.check_output(["lean", "--print-prefix"], cwd=root, text=True).strip()
    if binary.resolve() != (Path(installed) / "bin/lean").resolve():
        parser.error("recorded Lean binary does not match the active toolchain; rebuild first")
    if not setup.exists():
        parser.error("missing module setup; build first")
    setup_data = json.loads(setup.read_text())
    if setup_data["name"] != args.module:
        parser.error("module setup name mismatch")
    # Reject copied traces that still refer to a different checkout.
    original_source = root / relative.with_suffix(".lean")
    if str(original_source) not in words:
        parser.error("recorded invocation belongs to another checkout; rebuild first")
    output = args.output.resolve() / args.label / args.module
    if (output / "runs.jsonl").exists():
        parser.error("results already exist; use a new label to avoid mixing experiments")
    output.mkdir(parents=True, exist_ok=True)
    provenance = {
        "module": args.module, "label": args.label, "root": str(root),
        "source": str(source), "source_sha256": digest(source),
        "setup_sha256": digest(setup), "platform": platform.platform(),
        "lean": subprocess.check_output([str(binary), "--version"], text=True).strip(),
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
        "lean_path": env.get("LEAN_PATH"),
        "plugins": [{"path": str(path), "sha256": digest(path)} for path in plugins],
    }
    for index in range(args.warmup + args.runs):
        run_dir = output / f"run-{index:02d}"
        run_dir.mkdir(exist_ok=True)
        command = list(words)
        command[command.index(str(original_source))] = str(source)
        for flag, suffix in [("-o", ".olean"), ("-i", ".ilean"), ("-c", ".c")]:
            if flag in command:
                command[command.index(flag) + 1] = str(run_dir / (relative.name + suffix))
        if args.profile:
            command += ["--profile", "-Dprofiler.threshold=10"]
        if args.trace:
            command += ["-Dtrace.profiler=true", "-Dtrace.profiler.threshold=10",
                        f"-Dtrace.profiler.output={run_dir / 'profile.json'}"]
        command += ["-D" + option for option in args.option]
        for plugin in plugins:
            command += ["--plugin", str(plugin)]
        log = run_dir / "lean.log"
        stderr_log = run_dir / "lean.stderr"
        start = time.monotonic()
        with log.open("wb") as handle, stderr_log.open("wb") as error_handle:
            process = subprocess.Popen(command, cwd=root, env=env, stdout=handle,
                                       stderr=error_handle)
            sampler = None
            if args.sample:
                sampler = subprocess.Popen(
                    ["/usr/bin/sample", str(process.pid), "2", "1", "-mayDie",
                     "-file", str(run_dir / "sample.txt")],
                    stdout=error_handle, stderr=error_handle)
            timed_out = False
            while True:
                pid, status, usage = os.wait4(process.pid, os.WNOHANG)
                if pid:
                    break
                if time.monotonic() - start > args.timeout:
                    timed_out = True
                    process.kill()
                    _, status, usage = os.wait4(process.pid, 0)
                    break
                time.sleep(0.01)
            process.returncode = os.waitstatus_to_exitcode(status)
        elapsed = time.monotonic() - start
        sample_exit = sampler.wait() if sampler else None
        record = provenance | {
            "index": index, "warmup": index < args.warmup, "command": command,
            "wall_seconds": elapsed, "user_seconds": usage.ru_utime,
            "system_seconds": usage.ru_stime,
            "peak_rss_bytes": usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024),
            "exit_code": process.returncode, "log": str(log),
            "stderr": str(stderr_log),
            "timed_out": timed_out,
            "sample_exit_code": sample_exit,
        }
        with (output / "runs.jsonl").open("a") as handle:
            handle.write(json.dumps(record) + "\n")
        print(json.dumps({key: record[key] for key in
                          ("module", "label", "index", "warmup", "wall_seconds", "exit_code")}),
              flush=True)
        if process.returncode:
            errors = []
            for line in log.read_text(errors="replace").splitlines():
                try:
                    message = json.loads(line)
                except ValueError:
                    continue
                if message.get("severity") == "error":
                    errors.append(str(message.get("data", message)))
            print("\n".join(errors)[-6000:] or log.read_text(errors="replace")[-6000:],
                  file=sys.stderr)
            print(stderr_log.read_text()[-6000:], file=sys.stderr)
            return process.returncode
        if sample_exit not in (None, 0):
            print(stderr_log.read_text()[-6000:], file=sys.stderr)
            return sample_exit
    return 0


if __name__ == "__main__":
    sys.exit(main())
