#!/usr/bin/env python3
"""Validate agent documentation references against the actual codebase.

Checks:
1. File path references: every *.lean path mentioned in docs exists on disk
2. Tactic coverage: every `macro "name" : tactic` in ProgramLogic/ is documented
3. Notation coverage: every `notation`/`scoped notation` in VCVio/ is documented
4. Dead references: no doc references to files that were deleted/renamed

Exit code 0 if all checks pass, 1 if any fail.
"""

import os
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

DOC_FILES = list((REPO_ROOT / "docs" / "agents").glob("*.md")) + [
    REPO_ROOT / "AGENTS.md",
    REPO_ROOT / "README.md",
    REPO_ROOT / "REFERENCES.md",
]

PROGRAM_LOGIC_DIR = REPO_ROOT / "VCVio" / "ProgramLogic"
VCVIO_DIR = REPO_ROOT / "VCVio"

LEAN_PATH_RE = re.compile(
    r'`(?:VCVio|Examples|ToMathlib|LibSodium)/[A-Za-z0-9_/]+\.lean`'
    r'|(?:VCVio|Examples|ToMathlib|LibSodium)/[A-Za-z0-9_/]+\.lean'
)

TACTIC_MACRO_RE = re.compile(r'(?:macro|syntax)\s+"([\w\']+)".*:\s*tactic')

NOTATION_RE = re.compile(
    r'(?:scoped\s+)?notation(?:\s*:\s*\d+)?\s+'
    r'(?:\(name\s*:=\s*\w+\)\s*)?'
    r'"([^"]+)"'
)


def read_all_docs() -> str:
    """Read and concatenate all documentation files."""
    contents = []
    for f in DOC_FILES:
        if f.exists():
            contents.append(f.read_text())
    return "\n".join(contents)


def check_file_paths(doc_text: str) -> list[str]:
    """Check that all Lean file paths mentioned in docs exist."""
    errors = []
    matches = LEAN_PATH_RE.findall(doc_text)
    seen = set()
    for match in matches:
        path_str = match.strip("`").strip()
        if path_str in seen:
            continue
        seen.add(path_str)
        full_path = REPO_ROOT / path_str
        if not full_path.exists():
            errors.append(f"Dead file reference: {path_str}")
    return errors


def find_tactic_macros() -> set[str]:
    """Find all tactic macro declarations in ProgramLogic/."""
    macros = set()
    for lean_file in PROGRAM_LOGIC_DIR.rglob("*.lean"):
        text = lean_file.read_text()
        for m in TACTIC_MACRO_RE.finditer(text):
            macros.add(m.group(1))
    return macros


def check_tactic_coverage(doc_text: str) -> list[str]:
    """Check that all tactic macros are mentioned in docs."""
    errors = []
    macros = find_tactic_macros()
    for macro in sorted(macros):
        if macro not in doc_text:
            errors.append(
                f"Undocumented tactic: `{macro}` "
                f"(defined in VCVio/ProgramLogic/)"
            )
    return errors


def find_notations() -> list[tuple[str, str]]:
    """Find notation declarations in VCVio/."""
    notations = []
    for lean_file in VCVIO_DIR.rglob("*.lean"):
        text = lean_file.read_text()
        rel_path = lean_file.relative_to(REPO_ROOT)
        for m in NOTATION_RE.finditer(text):
            notations.append((m.group(1).strip(), str(rel_path)))
    return notations


def check_notation_coverage(doc_text: str) -> list[str]:
    """Check that notations are mentioned in docs."""
    errors = []
    notations = find_notations()
    for symbol, source_file in notations:
        if len(symbol) < 2:
            continue
        if symbol not in doc_text:
            errors.append(
                f"Undocumented notation: `{symbol}` "
                f"(defined in {source_file})"
            )
    return errors


def main():
    if not DOC_FILES:
        print("ERROR: No documentation files found")
        sys.exit(1)

    doc_text = read_all_docs()
    all_errors: list[str] = []

    print("Checking file path references...")
    all_errors.extend(check_file_paths(doc_text))

    print("Checking tactic coverage...")
    all_errors.extend(check_tactic_coverage(doc_text))

    print("Checking notation coverage...")
    all_errors.extend(check_notation_coverage(doc_text))

    if all_errors:
        print(f"\n{len(all_errors)} issue(s) found:\n")
        for err in all_errors:
            print(f"  - {err}")
        sys.exit(1)
    else:
        print("\nAll documentation checks passed.")
        sys.exit(0)


if __name__ == "__main__":
    main()
