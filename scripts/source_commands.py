"""Index non-declaration syntax and proof commands at the formal Git revision.

Offsets are half-open byte ranges in the original blobs; lines are 1-based,
including the terminal period (the Abort period for a printing example).
`command` preserves notation patterns, expansions and format strings. For tactics
only the signature is shown: their proof role, not Ltac source, is to be ported.
Run with --write to refresh port/source-commands.tsv; the default checks it.
"""
import argparse
from bisect import bisect_left
from collections import Counter
import os
from pathlib import Path
import re

from source_contract import FORMAL, ROOT, git, source_modules


# Rocq quotes double themselves. A qualified/projected name's dot, and the
# two dots for recursive notations, are not sentence stops.
STRING = r'"(?:[^"]|"")*"'
TOKENS = re.compile(STRING.encode() + rb'|"|\(\*|\*\)|(?<!\.)\.{1,3}(?=\s|\Z)')
FOCUS = re.compile(rb'[\s+*{}-]*')
MODIFIERS = re.compile(r'(?:(?:#\[[^\]]+\]|\b(?:Local|Global)\b)\s*)+')


def sentences(data: bytes):
    """Yield (first byte, past last byte, comment-masked text) for each sentence."""
    masked = bytearray(data)
    depth = previous = 0
    for m in TOKENS.finditer(data):
        token = m[0]
        if token == b'(*':
            if depth == 0:
                comment = m.start()
            depth += 1
        elif token == b'*)':
            if depth == 0:
                raise ValueError(f"unmatched comment terminator at byte {m.start()}")
            depth -= 1
            if depth == 0:
                masked[comment:m.end()] = b' ' * (m.end() - comment)
        elif token == b'"':
            raise ValueError(f"unterminated string at byte {m.start()}")
        elif not depth and token in (b'.', b'...'):
            start = FOCUS.match(masked, previous).end()
            yield start, m.end(), masked[start:m.end()].decode()
            previous = m.end()
    if depth or masked[previous:].strip():
        raise ValueError(f"unterminated comment or sentence after byte {previous}")


def one_line(text):
    # Whitespace in Rocq's quoted 'format' layouts (especially repeated spaces)
    # is meaningful. Only normalize whitespace *outside* quoted strings.
    return re.sub(STRING + r'|\s+', lambda m: ' ' if m[0].isspace() else m[0], text)


def role(command):
    if re.match(r'(?:Notation|Infix)\b', command):
        if 'only printing' in command:
            return 'pretty-printer'
        if 'only parsing' in command:
            return 'parser-only notation'
        if re.match(r'Notation\s+[^"\s]', command):
            return 'term abbreviation'
        return 'term notation'
    if command.startswith('Declare Custom Entry '):
        return 'syntax category'
    if re.match(r'(?:Open|Close|Bind|Declare|Delimit) Scope\b', command):
        return 'notation scope'
    if re.match(r'(?:Import|Export)\b', command) and re.search(r'\b\w*Notations?\b', command):
        return 'notation scope'
    if command.startswith('Coercion '):
        return 'elaboration coercion'
    if command.startswith('Tactic Notation '):
        return 'tactic syntax'
    if command.startswith('Ltac '):
        return 'proof tactic'
    if command.startswith('Hint '):
        return 'proof search/rewrite rule'
    if command.startswith('Existing Instance '):
        return 'instance search registration'
    if (re.match(r'(?:Opaque|Transparent)\b', command)
            or command.startswith('Arguments ') and ': simpl ' in command):
        return 'proof reduction control'
    if re.match(r'(?:Set|Unset) Printing\b|Print\b', command):
        return 'proof display'
    if command.startswith('Set Warnings ') and 'notation-' in command:
        return 'notation diagnostic setting'
    return None


def module_rows(path, data):
    file_module = 'Vellvm.' + path.removeprefix('src/rocq/').removesuffix('.v').replace('/', '.')
    newlines = [m.start() for m in re.finditer(b'\n', data)]
    stack = []
    probe = None
    for start, end, text in sentences(data):
        text = one_line(text)
        command = MODIFIERS.sub('', text, count=1) if MODIFIERS.match(text) else text
        block = re.match(r'(Module(?: Type)?|Section)\s+(?:(?:Import|Export)\s+)?(\w+)\b', command)
        if block and ':=' not in command:
            stack.append(block.groups())
        elif close := re.fullmatch(r'End (\w+)\s*\.', command):
            if not stack or stack.pop()[1] != close[1]:
                raise ValueError(f'{path}:{start}: unbalanced {command}')
        if command.startswith('Goal '):
            if probe or path != 'src/rocq/Syntax/SurfaceSyntax.v':
                raise ValueError(f'{path}:{start}: unexpected anonymous {command}')
            probe = start, text
            continue
        if command == 'Abort.':
            if probe is None:
                raise ValueError(f'{path}:{start}: Abort with no printing probe')
            start, goal = probe
            text = goal + ' … Abort.'
            kind = 'printing example (no proof)'
            probe = None
        else:
            if probe and command in ('Qed.', 'Defined.', 'Admitted.'):
                raise ValueError(f'{path}:{start}: printing probe was not aborted')
            kind = role(command)
            if not kind:
                continue
            if kind in ('tactic syntax', 'proof tactic'):
                text = text.split(':=', 1)[0].strip()
        module = '.'.join([file_module, *(n for k, n in stack if k.startswith('Module'))])
        sections = '.'.join(n for k, n in stack if k == 'Section')
        text = text.replace('\\', '\\\\').replace('\t', '\\t').replace('\r', '\\r').replace('\n', '\\n')
        yield (path, module, sections, start, end, 1 + bisect_left(newlines, start),
               1 + bisect_left(newlines, end - 1), kind, text)
    if stack or probe:
        raise ValueError(f'{path}: unclosed scope or probe: {stack}, {probe}')


def inventory(repo):
    files, blobs = source_modules(repo, FORMAL)
    rows = []
    for path in files:
        try:
            rows.extend(module_rows(path, git(repo, 'cat-file', 'blob', blobs[path])))
        except ValueError as error:
            raise ValueError(f'{path}: {error}') from error
    probes = Counter(row[-1] for row in rows if row[-2] == 'printing example (no proof)')
    if probes != {'Goal P add_twice. … Abort.': 1, 'Goal P test_branch. … Abort.': 1}:
        raise ValueError(f'expected exactly the two SurfaceSyntax printing probes, got {probes}')
    header = 'source\tmodule\tsections\tbyte_start\tbyte_end\tline_start\tline_end\tlean_role\tcommand\n'
    return (header + ''.join('\t'.join(map(str, row)) + '\n' for row in rows)).encode()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    table = ROOT / 'port/source-commands.tsv'
    expected = inventory(Path(os.environ.get('VELLVM_SRC', ROOT.parent / 'vellvm')))
    if args.write:
        table.write_bytes(expected)
    elif not table.is_file() or table.read_bytes() != expected:
        raise SystemExit(f'source command inventory mismatch: {table}')
    print(f'{expected.count(bytes([10])) - 1} source commands; 2 aborted printing examples included')
