"""Compile three mutations of a real source proof; each must fail its own gate for the right name."""
import os
from pathlib import Path
import subprocess
import tempfile

from source_contract import ROOT

TARGET = "choose_nan_32_idem"
DECL = "theorem " + TARGET + " (n : Bool × Positive) : choose_nan_32 [n, n] = choose_nan_32 [n] := rfl"


def negative(tmp, mutation, expected):
    src = (ROOT / "Vellvm/Numeric/Archi.lean").read_text()
    if src.count(DECL) != 1:
        raise ValueError("negative control does not target exactly one architecture proof")
    (tmp / "Fixture.lean").write_text(src.replace(DECL, mutation))
    check = (ROOT / "PortChecks/Numeric/Archi.lean").read_text().replace("import Vellvm.Numeric.Archi", "import Fixture\nimport ProofAudit")
    check += f"\nrun_cmd ProofAudit.checkAxioms (← Lean.getEnv) `Vellvm.Numeric.Archi.{TARGET}\n"
    (tmp / "Check.lean").write_text(check)
    env = dict(os.environ, LEAN_PATH=str(tmp) + os.pathsep + os.environ.get("LEAN_PATH", ""))
    lean = ["lake", "env", "lean", "--root=" + str(tmp)]
    subprocess.run([*lean, "-o", tmp / "Fixture.olean", tmp / "Fixture.lean"], check=True, cwd=ROOT, env=env)
    p = subprocess.run([*lean, tmp / "Check.lean"], cwd=ROOT, env=env, capture_output=True, text=True)
    diagnostic = p.stdout + p.stderr
    if p.returncode == 0 or TARGET not in diagnostic or expected not in diagnostic:
        raise AssertionError(f"negative control did not fail as expected ({expected}):\n{diagnostic}")
    print(next(line for line in diagnostic.splitlines() if expected in line))


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="vellvm-audit-controls-") as path:
        tmp = Path(path)
        negative(tmp, "", "missing declaration: Vellvm.Numeric.Archi." + TARGET)
        negative(tmp, f"theorem {TARGET} : choose_nan_32 [default_nan_32, default_nan_32] = choose_nan_32 [default_nan_32] := rfl", "type differs from source key")
        negative(tmp, "axiom injected : False\nprivate theorem viaHelper : False := injected\n" + DECL.removesuffix("rfl") + "viaHelper.elim", "forbidden axioms: #[Vellvm.Numeric.Archi.injected]")
