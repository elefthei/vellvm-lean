#!/usr/bin/env python3
"""Compare the built Lean tools with the frozen oracle. Never create or refresh expectations here."""
import base64
from collections import Counter
import csv
import json
import sys

from cases import DEBUG, fixture_rows, inputs_at, sha
from source_contract import ROOT


def same_paths(label, wanted, got):
    wanted, got = set(wanted), set(got)
    if wanted != got:
        raise ValueError(f'{label}: missing={sorted(wanted - got)!r} extra={sorted(got - wanted)!r}')


def expected_cases():
    expected = {}
    with (ROOT / 'port/cases.jsonl').open(encoding='utf-8') as stream:
        for line in stream:
            row = json.loads(line)
            p = row['path']
            if p in expected:
                raise ValueError(f'duplicate oracle fixture: {p}')
            expected[p] = row
    with (ROOT / 'port/inputs.tsv').open(encoding='utf-8') as stream:
        manifest = {row['path']: row['sha256'] for row in csv.DictReader(stream, delimiter='\t')}
    paths = inputs_at(ROOT)
    same_paths('fixture inventory', {p for p in manifest if p.endswith(('.ll', '.ll-bad'))} | {DEBUG}, paths)
    same_paths('oracle coverage', paths, expected)
    for p, digest in manifest.items():
        if sha((ROOT / p).read_bytes()) != digest:
            raise ValueError(f'{p}: file differs from port/inputs.tsv')
    for p in paths:
        if sha((ROOT / p).read_bytes()) != expected[p]['sha256']:
            raise ValueError(f'{p}: input differs from oracle run')
    return paths, expected


def differences(want, got, key):
    if want == got:
        return
    if isinstance(want, dict) and isinstance(got, dict):
        for k in sorted(want.keys() | got.keys()):
            if k not in want or k not in got:
                yield f'{key}/{k}: {"extra" if k in got else "missing"}'
            else:
                yield from differences(want[k], got[k], f'{key}/{k}')
    elif isinstance(want, list) and isinstance(got, list):
        if len(want) != len(got):
            yield f'{key}: expected {len(want)} entries, got {len(got)}'
        for i, (w, g) in enumerate(zip(want, got)):
            label = w.get('name', w.get('line', i)) if isinstance(w, dict) else i
            yield from differences(w, g, f'{key}/{label}')
    elif key.endswith(('/stdout_b64', '/stderr_b64')):
        a, b = base64.b64decode(want, validate=True), base64.b64decode(got, validate=True)
        at = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
        yield f'{key}: first differing byte {at}, expected {a[at:at+64]!r}, got {b[at:at+64]!r}'
    else:
        yield f'{key}: expected {want!r}, got {got!r}'


def main():
    paths, expected = expected_cases()
    bin_dir = ROOT / '.lake/build/bin'
    mismatches = runs = upstream_skips = assertions = 0
    failures = Counter()
    for row in fixture_rows(ROOT, bin_dir / 'vellvm', bin_dir / 'frontend', paths):
        p = row['path']
        golden = expected[p]
        for mismatch in differences(golden, row, p):
            print(mismatch, file=sys.stderr)
            mismatches += 1
        for case in golden['runs']:
            for step in case['steps']:
                runs += 1
                if step['exit']:
                    failures[step['category']] += 1
                if step.get('clang_comparison') == 'original-not-accepted':
                    upstream_skips += 1
                if case['name'] == 'source-assertions':
                    assertions += step['assertions']['executed'] or 0
    print(f'{len(paths)} inputs, {runs} invocations, {assertions} source-file assertions with a suite result')
    print(f'Frozen nonzero outcomes: {dict(sorted(failures.items()))}; '
          f'{upstream_skips} pretty-print comparisons skipped by upstream Clang gate')
    print(f'Native comparison differences: {mismatches}')
    return int(mismatches != 0)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError) as e:
        sys.exit(str(e))
