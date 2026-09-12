#!/usr/bin/env python3
"""Coordinate upstream Lean linters and maintain an exact, shrink-only exception baseline."""

from __future__ import annotations

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


BASELINE = Path("scripts/nolints.json")
TEST_ROOTS = ("VCVioTest", "LatticeCryptoTest", "HashSigTest")


def run(*args: str, **kwargs) -> subprocess.CompletedProcess:
    return subprocess.run(args, check=True, text=True, **kwargs)


def read_pairs(text: str, label: str) -> set[tuple[str, str]]:
    data = json.loads(text)
    if not isinstance(data, list) or any(
        not isinstance(pair, list) or len(pair) != 2
        or any(not isinstance(value, str) or not value for value in pair)
        for pair in data
    ):
        raise ValueError(f"{label}: expected an array of [linter, declaration] pairs")
    pairs = {tuple(pair) for pair in data}
    if len(pairs) != len(data):
        raise ValueError(f"{label}: duplicate exception entries")
    return pairs


def executable(target: str) -> str:
    output = run("lake", "query", target, stdout=subprocess.PIPE).stdout.strip()
    path = Path(output)
    if not path.is_file():
        raise ValueError(f"Lake did not return an executable for {target}: {output}")
    return str(path.resolve())


def git_files() -> list[tuple[str, str]]:
    entries = run("git", "ls-files", "--stage", "-z", stdout=subprocess.PIPE).stdout
    result = []
    for entry in entries.split("\0"):
        if not entry:
            continue
        metadata, path = entry.split("\t", 1)
        mode, _, stage = metadata.split()
        if stage != "0":
            raise ValueError(f"Unresolved index entry: {path}")
        result.append((mode, path))
    untracked = run("git", "ls-files", "--others", "--exclude-standard", "-z",
                    stdout=subprocess.PIPE).stdout
    for path in filter(None, untracked.split("\0")):
        mode = "100755" if Path(path).stat().st_mode & 0o111 else "100644"
        result.append((mode, path))
    return result


def style_modules(files: list[tuple[str, str]], roots: list[str]) -> dict[str, list[str]]:
    groups = {root: [] for root in roots}
    folded = {}
    for mode, path in files:
        key = path.casefold()
        if key in folded and folded[key] != path:
            raise ValueError(f"Case-insensitive filename clash: {folded[key]}, {path}")
        folded[key] = path
        if not path.endswith(".lean"):
            continue
        if mode == "100755":
            raise ValueError(f"Executable Lean source: {path}")
        module = path[:-5].replace("/", ".")
        root = module.split(".", 1)[0]
        if root in groups and Path(path).is_file():
            groups[root].append(module)
    if any(not modules for modules in groups.values()):
        raise ValueError("Style coverage has an empty source root")
    return {root: sorted(set(modules)) for root, modules in groups.items()}


def style(libraries: list[str]) -> None:
    # Interop keeps its existing source-only coverage; it is never imported or built here.
    groups = style_modules(git_files(), [*libraries, *TEST_ROOTS, "Interop"])
    tool = executable("mathlib/lint-style")
    with tempfile.TemporaryDirectory(prefix="vcvio-style-") as directory:
        scratch = Path(directory)
        inputs = []
        for root, modules in groups.items():
            module = f"{root}.VCVioLintInput"
            path = scratch / root / "VCVioLintInput.lean"
            path.parent.mkdir(parents=True)
            path.write_text("".join(f"import {name}\n" for name in modules))
            inputs.append(module)
        # The pinned upstream CLI lints imports of its input modules. These temporary lists
        # cover leaf tests too, without compiling executable modules with colliding mains.
        env = dict(os.environ)
        env["LEAN_SRC_PATH"] = str(scratch) + os.pathsep + env.get("LEAN_SRC_PATH", "")
        run(tool, *inputs, env=env)
    print(f"Style checked {sum(map(len, groups.values()))} source files.", flush=True)


def collect(tool: str, libraries: list[str], baseline: str) -> set[tuple[str, str]]:
    current = set()
    for library in libraries:
        with tempfile.TemporaryDirectory(prefix="vcvio-env-lint-") as directory:
            scratch = Path(directory)
            path = scratch / BASELINE
            path.parent.mkdir()
            path.write_text(baseline)
            result = run(tool, "--update", "--no-build", library, cwd=scratch,
                         stdout=subprocess.PIPE)
            # A successful complete run writes the JSON before printing this marker.
            if f"-- Linting passed for {library}." not in result.stdout:
                raise ValueError(f"Incomplete linter output for {library}: {result.stdout}")
            current.update(read_pairs(path.read_text(), library))
            print(result.stdout, end="", flush=True)
    return current


def check_delta(current: set, baseline: set, *, prune: bool) -> None:
    new = current - baseline
    stale = baseline - current
    if new:
        raise ValueError("Unlisted lint findings:\n" + format_pairs(new))
    if stale and not prune:
        raise ValueError("Obsolete lint exceptions:\n" + format_pairs(stale)
                         + "\nRun lake lint -- --prune-baseline to remove them.")


def format_pairs(pairs: set) -> str:
    return "\n".join(f"  {linter}: {name}" for linter, name in sorted(pairs))


def write_baseline(path: Path, pairs: set) -> None:
    # Replace only after every library has completed and additions have been rejected.
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, prefix=".nolints-",
                                     delete=False) as output:
        temporary = Path(output.name)
        try:
            output.write("[" + ",\n ".join(json.dumps(pair, ensure_ascii=False)
                                           for pair in sorted(pairs)) + "]\n")
            output.flush()
            os.fsync(output.fileno())
            temporary.chmod(path.stat().st_mode & 0o777)
            os.replace(temporary, path)
        finally:
            temporary.unlink(missing_ok=True)


def environment(libraries: list[str], *, no_build: bool, prune: bool,
                base_ref: str | None) -> None:
    baseline_text = BASELINE.read_text()
    baseline = read_pairs(baseline_text, str(BASELINE))
    if base_ref:
        base = run("git", "merge-base", "HEAD", base_ref, stdout=subprocess.PIPE).stdout.strip()
        previous = run("git", "show", f"{base}:{BASELINE}", stdout=subprocess.PIPE).stdout
        additions = baseline - read_pairs(previous, base_ref)
        if additions:
            raise ValueError("Lint baseline additions relative to the merge base:\n"
                             + format_pairs(additions))
    if not no_build:
        run("lake", "build", *libraries)
    current = collect(executable("batteries/runLinter"), libraries, baseline_text)
    check_delta(current, baseline, prune=prune)
    if prune and current != baseline:
        write_baseline(BASELINE, current)
        print(f"Removed {len(baseline - current)} obsolete lint exceptions.")
    print(f"Exact lint baseline: {len(current)} entries {dict(sorted(Counter(k for k, _ in current).items()))}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--libraries", required=True, help="Default proof libraries supplied by Lake")
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--style-only", action="store_true")
    modes.add_argument("--env-only", action="store_true")
    modes.add_argument("--prune-baseline", action="store_true")
    parser.add_argument("--no-build", action="store_true", help="Require already-built proof oleans")
    parser.add_argument("--base-ref", help="Also reject baseline additions against this merge base")
    args = parser.parse_args()
    libraries = args.libraries.split(",")
    if not all(libraries) or len(libraries) != len(set(libraries)):
        parser.error("Expected a nonempty list of distinct proof libraries")
    try:
        if not args.env_only and not args.prune_baseline:
            style(libraries)
        if not args.style_only:
            environment(libraries, no_build=args.no_build, prune=args.prune_baseline,
                        base_ref=args.base_ref)
    except subprocess.CalledProcessError as error:
        if error.stdout:
            print(error.stdout, end="", file=sys.stderr)
        return error.returncode if 0 < error.returncode < 126 else 1
    except (OSError, ValueError) as error:
        print(f"lint: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
