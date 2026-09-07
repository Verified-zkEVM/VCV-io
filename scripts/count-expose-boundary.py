#!/usr/bin/env python3
"""Count files with exposed public sections, ignoring Lean comments and literals.

This is a lexical check, not elaboration: macro-generated sections are outside its scope.
"""

from pathlib import Path
import re
import sys


TOKEN = re.compile(
    r'--[^\n]*|/-|-/'
    r'|r(?P<hashes>#+)".*?"(?P=hashes)|r".*?"'
    r'|"(?:\\.|[^"\\])*"|«[^»]*»'
    r"|'(?:\\.|[^'\\])'"
    r"|[^\W\d][\w'.]*|@\[|\S",
    re.DOTALL,
)


def tokens(source: str) -> list[str]:
    result = []
    depth = 0
    # Inside block comments only delimiters have meaning (quotes are ordinary text).
    position = 0
    while position < len(source):
        if depth:
            marker = re.search(r'/-|-/', source[position:])
            if marker is None:
                break
            depth += 1 if marker[0] == '/-' else -1
            position += marker.end()
            continue
        match = TOKEN.search(source, position)
        if match is None:
            break
        position = match.end()
        token = match[0]
        if token == '/-':
            depth = 1
        elif not token.startswith('--'):
            # Keep literals as whole tokens so their contents cannot match commands.
            result.append(token)
    return result


def broadly_exposed(path: Path) -> bool:
    stream = tokens(path.read_text(encoding='utf-8'))
    # Lean.Parser.Command.sectionHeader permits expose, public, noncomputable, meta,
    # in that order. Attributes on declarations are deliberately not matched here.
    for start in range(len(stream)):
        if stream[start:start + 4] != ['@[', 'expose', ']', 'public']:
            continue
        end = start + 4
        for modifier in ('noncomputable', 'meta'):
            if stream[end:end + 1] == [modifier]:
                end += 1
        if stream[end:end + 1] == ['section']:
            return True
    return False


if __name__ == '__main__':
    root = Path(sys.argv[1])
    for library in sorted(sys.argv[2:]):
        directory = root / library
        if directory.is_dir():
            count = sum(broadly_exposed(path) for path in directory.rglob('*.lean'))
            print(f'{library}\t{count}')
