"""Read only immutable Git objects. Run directly to check, or pass --write to refresh."""
import argparse
import os
from pathlib import Path
import subprocess

FORMAL = "3a6f23d33602b3d677b5b5f9088b9a32adf7dc7d"
ORACLE = "7f0610c38d829b79bf6e867edf410c9e6f928f98"
TEST_TREE = "b044378a39d481a0cbcbe131ddc3254c58fbdd00"
ROOT = Path(__file__).resolve().parents[1]
DRIVERS = {"src/ml/extracted/Extract.v": "vellvm", "src/ml/extracted/ExtractFrontend.v": "frontend"}


def git(repo, *args):
    return subprocess.check_output(["git", "-C", repo, *args])


def source_modules(repo, rev):
    entries = git(repo, "ls-tree", "-r", "--full-tree", "-z", rev).split(b"\0")
    blobs = {}
    for entry in filter(None, entries):
        header, name = entry.split(b"\t", 1)
        if name.endswith(b".v"):
            blobs[name.decode()] = header.split()[2].decode()
    project = git(repo, "show", rev + ":src/_RocqProject").decode().splitlines()
    files = ["src/" + line.removeprefix("./") for line in project if line.endswith(".v")]
    if len(files) != len(set(files)) or len(files) != 85:
        raise ValueError(f"{rev}: expected 85 distinct formal modules; got {len(set(files))}")
    diff = set(blobs) ^ (set(files) | DRIVERS.keys())
    if diff:
        raise ValueError(f"{rev}: unaccounted-for or missing sources: {sorted(diff)}")
    tree = git(repo, "rev-parse", rev + ":tests").decode().strip()
    tests = git(repo, "ls-tree", "-r", "-z", "--name-only", tree).split(b"\0")
    if tree != TEST_TREE or sum(p.endswith(b".ll") for p in tests) != 542:
        raise ValueError(f"{rev}: unexpected test tree {tree}")
    return files, blobs


def artifacts(repo):
    files, blobs = source_modules(repo, FORMAL)
    oracle_files, oracle_blobs = source_modules(repo, ORACLE)
    if set(files) != set(oracle_files):
        raise ValueError("formal and oracle module inventories differ")
    rows = ["source\tformal_blob\toracle_blob\trole\ttarget"]
    imports = []
    checks = []
    for file in [*files, *DRIVERS]:
        role = "extraction" if file in DRIVERS else "module"
        if role == "module":
            path = file.removeprefix("src/rocq/").removesuffix(".v").replace("/", ".")
            if path == "Utils.ITreeUtil":
                path = "Utils.CTreeUtil"
            target = "Vellvm." + path
            imports.append("import " + target)
            checks.append("import PortChecks." + path)
        else:
            target = DRIVERS[file]
        rows.append("\t".join((file, blobs[file], oracle_blobs[file], role, target)))
    return {
        "port/modules.tsv": rows,
        "Vellvm.lean": [*imports, "import Vellvm.Semantics.Model"],
        "PortChecks.lean": ["import Vellvm", *checks],
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    repo = Path(os.environ.get("VELLVM_SRC", ROOT.parent / "vellvm"))
    for name, lines in artifacts(repo).items():
        path = ROOT / name
        data = ("\n".join(lines) + "\n").encode()
        if args.write:
            path.parent.mkdir(exist_ok=True, parents=True)
            path.write_bytes(data)
        elif not path.is_file() or path.read_bytes() != data:
            raise SystemExit(f"source contract mismatch: {path}")
    print("85 formal modules and 2 extraction drivers reconciled at both pins")
