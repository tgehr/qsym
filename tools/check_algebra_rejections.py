#!/usr/bin/env python3
"""Reject corrupted arithmetic and denominator witnesses in the Lean kernel."""
import argparse
import os
import signal
from pathlib import Path
import subprocess
from export_audit import audit_export

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    cases = {
        "MergeWitness": "theorem bad : Raw.Added [([], (1,0))] [([], (1,0))] [([], (1,0))] := Raw.Added.both rfl (Raw.Added.nilLeft [])",
        "ScaleWitness": "theorem bad : Raw.Scaled (2,0) [([], (2,0))] [([], (3,0))] := Raw.Scaled.cons rfl Raw.Scaled.nil",
        "MappedCoefficient": "theorem bad : Raw.Mapped [(0,1)] (2,0) [([(1,1)], (2,0))] [([(0,1),(1,1)], (3,0))] := Raw.Mapped.cons rfl rfl Raw.Mapped.nil",
        "MappedMonomial": "theorem bad : Raw.Mapped [(0,1)] (2,0) [([(1,1)], (2,0))] [([(0,1),(1,2)], (4,0))] := Raw.Mapped.cons rfl rfl Raw.Mapped.nil",
        "Arrangement": "theorem bad : Raw.arrange [([(0,2)], (1,0)), ([(0,1),(1,1)], (2,0))] = [([(0,1),(1,1)], (1,0)), ([(0,2)], (2,0))] := rfl",
        "Addition": "theorem bad : ArithmeticEquality (add [([], (1,0))] [([], (1,0))]) [([], (1,0))] := Raw.addition_check _ _ _ rfl",
        "MappedCheck": "theorem bad : Raw.Mapped [(0,1)] (2,0) [([(1,1)], (2,0))] [([(0,1),(1,1)], (3,0))] := Raw.mappedSame_sound rfl",
        "MergeFuel": "theorem bad : Raw.Added [] [] [] := Raw.addedSame_sound (fuel := 0) rfl",
        "ComplexProduct": "theorem bad : ArithmeticEquality (mul [([], (1,1))] [([], (1,1))]) [([], (2,0))] := Raw.mul_check _ _ _ rfl",
        "Denominator": "theorem bad : value (fun _ => 0) (constant (0,0)) ≠ 0 := nonzero_constant _ (c := (0,0)) (of_decide_eq_true rfl)",
        "CrossProduct": "theorem bad : Raw.fractionSame (1,1) (1,2) = true := rfl",
    }
    directory = ROOT / "build/algebra-rejections"
    directory.mkdir(exist_ok=True)
    valid = {
        "LexicographicOrder": "example : compareMonomial [(0,2)] [(1,1)] = .lt := rfl",
        "MultiplicationValid": "example : ArithmeticEquality (mul [([(0,1)], (1,0)), ([(1,1)], (1,0))] [([(0,1)], (1,0)), ([(1,1)], (1,0))]) [([(0,1),(1,1)], (2,0)), ([(0,2)], (1,0)), ([(1,2)], (1,0))] := Raw.mul_check _ _ _ rfl",
        "ArrangementValid": "example : Raw.arrange [([(0,2)], (1,0)), ([(0,1),(1,1)], (2,0))] = [([(0,1),(1,1)], (2,0)), ([(0,2)], (1,0))] := rfl",
    }
    for name, claim in (valid | cases).items():
        source = "import QSym.RationalCertificate\nopen QSym QSym.AlgebraCertificate\n" + claim + "\n"
        audit_export(source, name)
        file = directory / (name + ".lean")
        file.write_text(source)
        process = subprocess.Popen([args.lake, "env", "lean", str(file)], cwd=ROOT / "lean",
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, start_new_session=True)
        try:
            output, _ = process.communicate(timeout=30)
        except BaseException:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            raise
        file.with_suffix(".log").write_text(output)
        if name in valid:
            if process.returncode:
                raise RuntimeError(f"{name} was rejected:\n{output}")
            print("Checked " + name, flush=True)
        else:
            if process.returncode == 0 or not any(message in output for message in ("type mismatch", "is false", "unsolved goals")):
                raise RuntimeError(f"{name} was not rejected for a bad witness:\n{output}")
            print("Rejected " + name, flush=True)
    for forbidden in ("by rfl", "qsym_cached% rfl", "native_decide", "sorry"):
        try:
            audit_export("example : True := " + forbidden)
        except RuntimeError:
            continue
        raise RuntimeError("audit admitted " + forbidden)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
