"""Rebuild the formal evidence in a fresh archive; never build in VELLVM_SRC."""

import argparse
import os
from pathlib import Path
import subprocess
import tempfile


FORMAL_REV = "3a6f23d33602b3d677b5b5f9088b9a32adf7dc7d"
FORMAL_SWITCH = os.environ.get("VELLVM_FORMAL_SWITCH", "vellvm-formal-3a6f23d3")
LOCK = Path(__file__).resolve().parents[1] / "port" / "formal-packages.tsv"
JOBS = 8
COMPILER = "ocaml-base-compiler.4.14.1"
REQUIRED = {
    "ocaml": "4.14.1", "dune": "3.23.1", "menhir": "20260209",
    "rocq-core": "9.2.0", "rocq-stdlib": "9.2.0", "coq-ext-lib": "0.13.2",
    "coq-paco": "4.2.3", "coq-flocq": "4.2.2", "rocq-equations": "1.3.2+9.2",
    "coq-itree": "dev", "rocq-coinduction": "dev",
}
PINS = {
    "coq-itree": "git+https://github.com/rogerburtonpatel/InteractionTrees.git#02534c7e2b4a5c6bb4e8c028245533701e1facb0",
    "rocq-coinduction": "git+https://github.com/damien-pous/coinduction.git#07d2a09f9cb971209683298e9f5b3f5031d98b3f",
}


def _run(*args, cwd=None, stdout=None):
    env = dict(os.environ, OPAMJOBS=str(JOBS), LC_ALL="C", TZ="UTC")
    for variable in ("MAKEFLAGS", "MFLAGS", "ROCQPATH", "ROCQCORELIB", "ROCQLIB", "COQPATH", "COQLIB"):
        env.pop(variable, None)
    return subprocess.run(args, check=True, env=env, cwd=cwd, stdout=stdout)


def _text(*args):
    return _run(*args, stdout=subprocess.PIPE).stdout.decode()


def package_inventory():
    """Return installed packages, not just requested solver constraints."""
    rows = {}
    output = _text("opam", "list", "--switch", FORMAL_SWITCH, "--installed", "--short",
                   "--columns=name,version,pin", "--separator=\t", "--color=never")
    for line in output.splitlines():
        name, version, *pin = (field.strip() for field in line.split("\t"))
        rows[name] = (version, *pin) if pin else (version, "")
    for name, version in REQUIRED.items():
        expected = version, PINS.get(name, "")
        if rows.get(name) != expected:
            raise ValueError(f"{FORMAL_SWITCH}: {name}: expected {expected}, found {rows.get(name)}")
    return "name\tversion\tpin\n" + "".join(
        f"{name}\t{version}\t{pin}\n" for name, (version, pin) in sorted(rows.items())
    )


def ensure_switch():
    """Create a dedicated named switch, or verify (never repin) an existing one."""
    locked = LOCK.read_text()
    if FORMAL_SWITCH not in _text("opam", "switch", "list", "--short").splitlines():
        repos = set(_text("opam", "repo", "list", "--all", "--short").splitlines())
        rocq = "rocq-released"
        if rocq not in repos:
            rocq += "=https://rocq-prover.org/opam/released"
        _run("opam", "switch", "create", "-y", "--no-switch", f"--repos={rocq},default",
             FORMAL_SWITCH, COMPILER)
        for name, url in PINS.items():
            _run("opam", "pin", "add", "--switch", FORMAL_SWITCH, "-yn", f"{name}.dev", url)
        versions = dict(line.split("\t")[:2] for line in locked.splitlines()[1:])
        _run("opam", "install", "--switch", FORMAL_SWITCH, "-y",
             *(f"{name}.{version}" for name, version in versions.items()))
    actual = package_inventory()
    if actual != locked:
        raise ValueError(f"installed packages in {FORMAL_SWITCH} differ from {LOCK}")


def compile_archive(archive: Path):
    """Use the upstream rocq target (the interp/extracted targets omit Theory)."""
    src = archive / "src"
    prefix = ["opam", "exec", "--switch", FORMAL_SWITCH, "--"]
    with (archive / "rocq-dep.mk").open("xb") as dep:
        _run(*prefix, "rocq", "dep", "-f", "_RocqProject", cwd=src, stdout=dep)
    # The pinned Makefile forwards an unbounded `-j` to the generated makefile.
    make = f'''MAKE=sh -c '[ "$$1" != -j ] || shift; exec make -j{JOBS} "$$@"' submake'''
    _run(*prefix, "make", "-C", "src", make, "rocq", cwd=archive)
    project = (src / "_RocqProject").read_text().splitlines()
    sources = {(src / line.strip()).resolve() for line in project if line.strip().endswith(".v")}
    if not sources or sources != {path.resolve() for path in (src / "rocq").rglob("*.v")}:
        raise ValueError("_RocqProject does not cover all formal source modules")
    for source in sorted(sources):
        for ext in (".vo", ".glob"):
            path = source.with_suffix(ext)
            if not path.is_file() or not path.stat().st_size:
                raise ValueError(f"missing elaboration evidence: {path}")


def build_formal(repo: Path, archive: Path):
    """Build the immutable revision at archive, which must not already exist."""
    if archive.resolve().is_relative_to(repo.resolve()):
        raise ValueError("the archive must be outside the Vellvm source checkout")
    ensure_switch()
    archive.mkdir(parents=True)
    with tempfile.TemporaryFile() as tar:
        _run("git", "-C", repo, "archive", "--format=tar", FORMAL_REV, stdout=tar)
        tar.seek(0)
        subprocess.run(["tar", "-xf", "-", "-C", archive], stdin=tar, check=True)
    compile_archive(archive)


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("archive", type=Path, help="new build directory, outside source checkout")
    cli.add_argument("--repo", type=Path, default=os.environ.get("VELLVM_SRC", "../vellvm"))
    args = cli.parse_args()
    build_formal(args.repo, args.archive)
