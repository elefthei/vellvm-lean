"""Materialize the pinned fixture corpus in an empty directory, emitting its TSV inventory."""

import argparse
from collections import Counter
from hashlib import sha256
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

from source_contract import FORMAL, ORACLE, ROOT, TEST_TREE, git


ROOTS = ("tests", "src/libll", "tractor", "utilities")
I1 = "tests/llvm-arith/i1"
GEN = f"{I1}/gen-i1.py"
GEN_DEPS = (GEN, "tests/gen.py", "tests/ub/fill-ub-lines.py")

# Only executable recipes differ from the source. Keep the .ll and historical READMEs intact.
RECIPES = {
    "tractor/c2rust-tests/arrays/Makefile": [
        (b"../../../src/vellvm", b"../../../.lake/build/bin/vellvm"),
    ],
    "tests/perf/run.sh": [
        (b"the binary at src/vellvm", b"the binary at .lake/build/bin/vellvm"),
        (b'vellvm="$src/vellvm"', b'vellvm="$src/../.lake/build/bin/vellvm"'),
        (b"run 'make' in src/ first", b"run 'lake build vellvm' at the repository root first"),
        (b'&& ./vellvm -L libll', b'&& "$vellvm" -L libll'),
    ],
    "tests/ub/compare.py": [
        (b"cd src && make interp            # builds ./vellvm", b"lake build vellvm                # from the repository root"),
        (b"python3 ../tests/ub/compare.py   # writes ../tests/ub/results/", b"python3 tests/ub/compare.py      # writes tests/ub/results/"),
        (b'os.path.join(REPO, "src", "vellvm")', b'os.path.join(REPO, ".lake", "build", "bin", "vellvm")'),
        (b'os.path.join(os.path.dirname(vellvm), "libll")', b'os.path.join(REPO, "src", "libll")'),
    ],
    "utilities/vellvm-reduce.sh": [
        (b'SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )\n\n', b''),
        (b'export VELLVM_EXE=$(PATH=$PATH:. which vellvm)\nif [[ $? != "0" ]]; then',
         b'SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)\n'
         b'export VELLVM_EXE="$SCRIPT_DIR/../.lake/build/bin/vellvm"\nif [[ ! -x "$VELLVM_EXE" ]]; then'),
    ],
}


def roles(name, data):
    if name.endswith(".ll-bad"):
        return "parser-validator"
    if not name.endswith(".ll"):
        if name.endswith((".sh", "/Makefile")) or name == "tests/ub/compare.py":
            return "recipe"
        if name in GEN_DEPS or "/gen-" in name:
            return "generator"
        return "companion"
    result = ["parse-print"]
    # This identifies source roles only. Assertion counts and outcomes come from the oracle.
    if re.search(rb"^[ \t]*;[ \t]*ASSERT[ \t]+(?:EQ[ \t]*:[^\n]*=|(?:SUCCEEDS|FAILS|UB[ \t]+[0-9]+)[ \t]*:)", data, re.M):
        result.append("assertion-directives")
    if re.search(rb'^[ \t]*define[ \t]+[^;\n]*@(?:main|"main")[ \t]*\(', data, re.M):
        result.append("main")
    if name.endswith(".srctgt.ll"):
        result.append("paired-src-tgt")
    if name.startswith(("src/libll/", "utilities/vaargs/printf-src/")):
        result.append("library")
    if name.startswith("tractor/"):
        result.append("linked-suite" if name.endswith("/array_tests.ll") else "link-input")
    if name.startswith("tests/perf/"):
        result.append("performance")
    return ",".join(result)


def prepare_inputs(repo: Path, dest: Path) -> bytes:
    """Read Git objects at the pins; write only inside dest (never the source checkout)."""
    repo, dest = repo.resolve(), dest.resolve()
    if dest.is_relative_to(repo) or (dest.exists() and any(dest.iterdir())):
        raise ValueError(f"expected an empty destination outside the source repository: {dest}")
    dest.mkdir(parents=True, exist_ok=True)
    tree = git(repo, "ls-tree", "-rz", FORMAL, "--", *ROOTS)
    if tree != git(repo, "ls-tree", "-rz", ORACLE, "--", *ROOTS):
        raise ValueError("formal and oracle fixture blobs or modes differ")
    if git(repo, "rev-parse", f"{FORMAL}:tests").decode().strip() != TEST_TREE:
        raise ValueError("unexpected upstream tests tree")
    rows = {}
    counts = Counter()
    for record in tree.rstrip(b"\0").split(b"\0"):
        header, raw_name = record.split(b"\t", 1)
        mode, kind, oid = header.decode().split()
        name = raw_name.decode()
        if kind != "blob" or mode not in {"100644", "100755"}:
            raise ValueError(f"unexpected fixture entry: {record!r}")
        data = git(repo, "cat-file", "blob", oid)
        source_sha = sha256(data).hexdigest()
        for before, after in RECIPES.get(name, ()):
            if data.count(before) != 1:
                raise ValueError(f"pinned recipe does not contain one {before!r}: {name}")
            data = data.replace(before, after)
        path = dest / name
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("xb") as f:
            f.write(data)
        path.chmod(int(mode[-3:], 8))
        if path.suffix in (".ll", ".ll-bad"):
            counts[name.split("/")[0], path.suffix] += 1
        rows[name] = [sha256(data).hexdigest(), roles(name, data), "tracked-recipe" if name in RECIPES else "tracked",
                      mode, source_sha, "", "", ""]
    if counts != {("tests", ".ll"): 542, ("tests", ".ll-bad"): 8, ("src", ".ll"): 3,
                  ("tractor", ".ll"): 5, ("utilities", ".ll"): 12} or not RECIPES.keys() <= rows.keys():
        raise ValueError(f"pinned fixture corpus mismatch: {counts}")

    makefile = git(repo, "show", f"{FORMAL}:src/Makefile").replace(b"\\\n", b" ")
    recipe = re.search(rb"^I1_TESTS := \$\(addprefix \$\(I1_DIR\)/,\s*([^)]*)\)$", makefile, re.M)
    names = recipe[1].decode().split() if recipe else []
    if len(names) != 13 or len(set(names)) != 13 or not all(re.fullmatch(r"[a-z-]+\.ll", n) for n in names):
        raise ValueError(f"unexpected i1 generation targets: {names}")
    # The generator rewrites every target. Run it away from the tracked inputs, even on a fresh export.
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        for dep in GEN_DEPS:
            (work / dep).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(dest / dep, work / dep)
        subprocess.run([sys.executable, GEN], cwd=work, check=True, stdout=sys.stderr,
                       env=dict(os.environ, LC_ALL="C", TZ="UTC", PYTHONHASHSEED="0", PYTHONPATH=""))
        if {p.name for p in (work / I1).glob("*.ll")} != set(names):
            raise ValueError("i1 generator outputs do not match src/Makefile")
        for basename in names:
            name = f"{I1}/{basename}"
            data = (work / name).read_bytes()
            digest = sha256(data).hexdigest()
            if name in rows:
                rows[name][2] = "tracked-generated"
            else:
                with (dest / name).open("xb") as f:
                    f.write(data)
                (dest / name).chmod(0o644)
                rows[name] = [digest, roles(name, data), "generated", "100644", "", "", "", ""]
            rows[name][-3:] = [GEN, rows[GEN][0], digest]

    header = "path\tsha256\trole\tprovenance\tmode\tsource_sha256\tgenerator\tgenerator_sha256\tgenerated_sha256\tsource_revision"
    lines = [header, *("\t".join([n, *rows[n], FORMAL]) for n in sorted(rows, key=os.fsencode))]
    return ("\n".join(lines) + "\n").encode()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("dest", type=Path)
    args = parser.parse_args()
    repo = Path(os.environ.get("VELLVM_SRC", ROOT.parent / "vellvm"))
    sys.stdout.buffer.write(prepare_inputs(repo, args.dest))
