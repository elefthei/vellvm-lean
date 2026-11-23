"""Build the two main-branch behavior oracles without touching their source checkout."""

import os
from pathlib import Path
import subprocess
import tempfile

from rocq_reference import COMPILER, JOBS
from source_contract import ORACLE, ROOT


SWITCH = f"vellvm-oracle-{ORACLE[:8]}"
LOCK = ROOT / "port" / "oracle-packages.tsv"
REQUIRED = {
    "ocaml": "4.14.1", "ocaml-base-compiler": "4.14.1", "dune": "3.23.1",
    "menhir": "20260209", "rocq-core": "9.2.0", "rocq-stdlib": "9.2.0",
    "rocq-equations": "1.3.2+9.2", "coq-flocq": "4.2.2", "coq-ext-lib": "0.13.2",
    "coq-paco": "4.2.3", "coq-itree": "5.2.1",
}


def _run(*args, **kwargs):
    env = dict(os.environ, OPAMJOBS=str(JOBS), LC_ALL="C", TZ="UTC")
    for name in ("OPAMSWITCH", "OPAM_SWITCH_PREFIX", "OCAMLPATH", "OCAML_TOPLEVEL_PATH",
                 "OCAMLTOP_INCLUDE_PATH", "CAML_LD_LIBRARY_PATH", "MAKEFLAGS", "MAKEFILES",
                 "MFLAGS", "ROCQPATH", "ROCQCORELIB", "ROCQLIB", "COQPATH", "COQLIB",
                 "COQFLAGS", "COQEXTRAFLAGS", "COQBIN", "ROCQBIN", "DUNE_BUILD_DIR"):
        env.pop(name, None)
    # Nested opam shells can leave *other* switches' compilers on PATH.
    env["PATH"] = os.pathsep.join(p for p in os.get_exec_path(env)
                                  if not (Path(p).parent / ".opam-switch").is_dir())
    return subprocess.run(args, check=True, env=env, **kwargs)


def _opam_lines(*args):
    return _run("opam", *args, stdout=subprocess.PIPE, text=True).stdout.splitlines()


def package_inventory() -> str:
    """Report the actual installed versions and pins, including transitive packages."""
    actual = _opam_lines("list", "--switch", SWITCH, "--installed", "--short", "--color=never",
                         "--columns=name,version,pin", "--separator=\t")
    found = []
    for line in actual:
        name, version, *pin = (field.strip() for field in line.split("\t"))
        found.append(f"{name}\t{version}\t{''.join(pin)}")
    found.sort()
    return "\n".join(["name\tversion\tpin", *found, ""])


def _ensure_switch():
    header, *lines = LOCK.read_text().splitlines()
    if header != "name\tversion\tpin":
        raise ValueError(f"unexpected package lock header in {LOCK}")
    packages = {}
    for line in lines:
        name, version, pin = line.split("\t")
        if pin or name in packages:
            raise ValueError(f"unexpected pin or duplicate in {LOCK}: {line}")
        packages[name] = version
    if not REQUIRED.items() <= packages.items():
        raise ValueError(f"missing or wrong required package in {LOCK}: {REQUIRED.items() - packages.items()}")
    if SWITCH not in _opam_lines("switch", "list", "--short"):
        repos = _opam_lines("repo", "list", "--all", "--short")
        rocq = "rocq-released" if "rocq-released" in repos else "rocq-released=https://rocq-prover.org/opam/released"
        _run("opam", "switch", "create", "--no-switch", "-y", f"--repos={rocq},default", SWITCH, COMPILER)
        _run("opam", "install", "--switch", SWITCH, "-y", *(f"{n}.{v}" for n, v in packages.items()))
    found = package_inventory().splitlines()[1:]
    if found != lines:
        raise ValueError(f"{SWITCH} differs from {LOCK}: missing {sorted(set(lines) - set(found))}; "
                         f"unexpected {sorted(set(found) - set(lines))}")


def build_oracles(repo: Path, out: Path) -> tuple[Path, Path]:
    """Return (interpreter, frontend) built from fresh out/main and out/frontend archives."""
    repo, out = repo.resolve(strict=True), out.resolve()
    if out.is_relative_to(repo):
        raise ValueError("the oracle build must be outside the source checkout")
    main, frontend = out / "main", out / "frontend"
    with tempfile.TemporaryFile() as tar:
        _run("git", "-C", repo, "archive", "--format=tar", ORACLE, stdout=tar)
        for archive in (main, frontend):
            archive.mkdir(parents=True)
            tar.seek(0)
            _run("tar", "-xf", "-", "-C", archive, stdin=tar)

    _ensure_switch()
    prefix = ("opam", "exec", "--switch", SWITCH, "--")
    src = main / "src"
    _run(*prefix, "make", "RocqMakefile", cwd=src)
    # GNU make's `private` keeps the compiler preload off every prerequisite.
    target = "rocq/Semantics/DynamicValues.vo"
    _run(*prefix, "make", "-f", "RocqMakefile", f"-j{JOBS}",
         f"--eval={target}: private OTHERFLAGS += -require Stdlib.ZArith.BinInt", target, cwd=src)

    # Bound the unbounded recursive `make -j` in both upstream extraction targets.
    submake = f'''MAKE=sh -c '[ "$$1" != -j ] || shift; exec make -j{JOBS} "$$@"' submake'''
    for archive, stamp, exe in ((main, "extracted", "main"),
                                (frontend, "ml/extracted/FRONTEND_STAMP", "frontend")):
        src = archive / "src"
        _run(*prefix, "make", submake, stamp, cwd=src)
        _run(*prefix, "dune", "build", "--profile", "release", f"ml/{exe}.exe", cwd=src)
        binary = src / "_build" / "default" / "ml" / f"{exe}.exe"
        if not binary.is_file() or not os.access(binary, os.X_OK):
            raise ValueError(f"missing oracle executable: {binary}")
    return (main / "src/_build/default/ml/main.exe", frontend / "src/_build/default/ml/frontend.exe")
