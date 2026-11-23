"""Regenerate proof coverage and behavior independently of any Lean binary or build cache."""
import argparse
from filecmp import cmp
import os
from pathlib import Path
import shutil
import tempfile

import cases
import declarations
import inputs
import oracle
import rocq_reference
import source_commands
from source_contract import ROOT, artifacts


def compare(expected, actual, name):
    if not actual.is_file() or not cmp(expected, actual, shallow=False):
        raise ValueError(f"reference mismatch: {name}")


def regenerate(repo, work, check):
    formal = work / "formal"
    rocq_reference.build_formal(repo, formal)
    main, frontend = oracle.build_oracles(repo, work / "oracles")
    corpus = work / "corpus"
    evidence = work / "evidence"
    evidence.mkdir()
    for name, lines in artifacts(repo).items():
        path = evidence / name
        path.parent.mkdir(exist_ok=True, parents=True)
        path.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    port = evidence / "port"
    (port / "formal-packages.tsv").write_bytes(rocq_reference.package_inventory().encode())
    (port / "oracle-packages.tsv").write_bytes(oracle.package_inventory().encode())
    (port / "declarations.tsv").write_bytes(declarations.generate(repo, formal).encode())
    (port / "source-commands.tsv").write_bytes(source_commands.inventory(repo))
    (port / "inputs.tsv").write_bytes(inputs.prepare_inputs(repo, corpus))
    for path in sorted(corpus.rglob("*")):
        if path.is_file():
            rel = path.relative_to(corpus)
            compare(path, ROOT / rel, rel)
    (corpus / "Examples").mkdir()
    shutil.copyfile(ROOT / "Examples/debug.ll", corpus / "Examples/debug.ll")
    cases.write_baseline(corpus, main, frontend, port / "cases.jsonl")
    for expected in sorted(evidence.rglob("*")):
        if expected.is_file():
            name = expected.relative_to(evidence)
            if check:
                compare(expected, ROOT / name, name)
            else:
                shutil.copyfile(expected, ROOT / name)
            print(f"{'checked' if check else 'wrote'} {name}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    os.environ.update(LC_ALL="C", TZ="UTC")
    repo = Path(os.environ.get("VELLVM_SRC", ROOT.parent / "vellvm")).resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix="vellvm-reference-") as temp:
        regenerate(repo, Path(temp), args.check)
