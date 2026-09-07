#!/usr/bin/env python3
"""Prepare ChatOps review instructions from a trusted checkout, without executing comment text."""

import argparse
import os
from pathlib import Path
import re
import uuid


def prepare_instructions(comment: str, profile: str) -> tuple[str, str] | None:
    """Return the review mode and instructions, or None for a different command."""
    match = re.fullmatch(r"/review(?:\s+(.*))?", comment, flags=re.DOTALL)
    if match is None:
        return None
    focus = (match.group(1) or "").strip()
    command = re.fullmatch(r"tactics(?:\s+(.*))?", focus, flags=re.DOTALL)
    if command is None:
        return "general", focus
    extra = (command.group(1) or "").strip()
    instructions = profile.rstrip()
    if extra:
        instructions += "\n\nAdditional review focus:\n" + extra
    return "tactics", instructions


def write_output(path: Path, name: str, value: str) -> None:
    """Use a fresh delimiter so user-provided newlines cannot inject workflow outputs."""
    delimiter = "review_" + uuid.uuid4().hex
    while delimiter in value:
        delimiter = "review_" + uuid.uuid4().hex
    with path.open("a", encoding="utf-8") as output:
        output.write(f"{name}<<{delimiter}\n{value}\n{delimiter}\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", type=Path, required=True)
    args = parser.parse_args()
    result = prepare_instructions(os.environ["COMMENT_BODY"], args.profile.read_text(encoding="utf-8"))
    output = Path(os.environ["GITHUB_OUTPUT"])
    write_output(output, "requested", "true" if result is not None else "false")
    if result is not None:
        mode, instructions = result
        write_output(output, "mode", mode)
        write_output(output, "instructions", instructions)


if __name__ == "__main__":
    main()
