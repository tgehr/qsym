#!/usr/bin/env python3
"""Check complete algebra exports against their exact scalar-rule dependencies.

Shared library modules may use tactics. Exported sources must contain only
proof terms. Timings include Lean startup, elaboration, kernel checks and axiom
audits, excluding compilation of shared dependencies; no proof cache is used.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time
from export_audit import audit_export

ROOT = Path(__file__).resolve().parents[1]
IMPORTS = ["Binding", "Refinement", "ProofCache", "AxiomCheck", "Numeric", "Tensor", "AC", "Bag",
           "TensorDomains", "Conditionals", "Dependent", "SummationBounds", "SummationAlgebra", "SummationLinearity",
           "SummationAffine", "SummationPowers", "SummationPrefix", "SummationMasks",
           "SummationTails", "SummationElementary", "SummationRoots"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", type=Path)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    if args.jobs < 1 or args.timeout < 1:
        parser.error("jobs and timeout must be positive")
    files = list(args.files)
    if not files:
        for suite, count in (("polynomial-summation", 14), ("weighted-summation", 16),
                             ("elementary-summation", 34), ("algebra-certificates", 13),
                             ("conditional-consumers", 31)):
            found = sorted((ROOT / "build" / suite).glob("*.lean"))
            if len(found) != count:
                parser.error(f"expected {count} certificates in build/{suite}; generate them first")
            files.extend(found)
    if not files:
        parser.error("generate certificates first")
    texts = [f.read_text() for f in files]
    for f, text in zip(files, texts):
        audit_export(text, str(f))
    replay = (ROOT / "lean/QSym/Replay.lean").read_text()
    region = (ROOT / "lean/QSym/Region.lean").read_text()
    needed = set(re.findall(r"Generated\.(r_\w+)", "\n".join(texts + [replay, region])))
    generated = (ROOT / "lean/QSym/Generated.lean").read_text()
    blocks = {name: text for text, name in re.findall(
        r"^(theorem (r_\w+)\b.*?^#qsym_check_axioms \2\b)", generated, re.M | re.S)}
    if needed - blocks.keys():
        raise RuntimeError(f"missing scalar dependencies: {needed - blocks.keys()}")
    out = ROOT / "build/export-check"
    out.mkdir(exist_ok=True)
    dependency = out / "ExportDependencies.lean"
    dependency_source = ("\n".join("import QSym." + m for m in IMPORTS)
        + "\nimport Mathlib.Data.Multiset.Fold\nnamespace QSym.Generated\n"
        + "\n\n".join(blocks[n] for n in blocks if n in needed) + "\nend QSym.Generated\n"
        + "\n".join(re.sub(r"^import [^\n]*\n", "", s, flags=re.M) for s in (replay, region)))
    dependency.write_text(dependency_source)
    env = os.environ.copy()
    env.pop("QSYM_PROOF_CACHE", None)
    command = [args.lake, "env", "lean", "-s", "65536"]
    subprocess.run([args.lake, "build"] + ["QSym." + m for m in IMPORTS + ["RationalCertificate"]], cwd=ROOT / "lean", env=env, check=True,
                   stdout=(out / "library.log").open("w"), stderr=subprocess.STDOUT)
    # Only shared dependencies are reused. Every exported theorem below is
    # freshly elaborated and kernel-checked. Lake first validates the complete
    # dependency closure, so direct-module hashes also detect upstream changes.
    digest = hashlib.sha256(dependency_source.encode())
    for module in IMPORTS:
        digest.update((ROOT / "lean/.lake/build/lib/lean/QSym" / (module + ".olean")).read_bytes())
    digest.update((ROOT / "lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Multiset/Fold.olean").read_bytes())
    fingerprint = digest.hexdigest()
    stamp = out / "dependencies.sha256"
    if not dependency.with_suffix(".olean").exists() or not stamp.exists() or stamp.read_text() != fingerprint:
        print("Compiling exact shared scalar dependencies", flush=True)
        with (out / "dependencies.log").open("w") as log:
            result = subprocess.run(command + ["--root=" + str(out), "-o", str(dependency.with_suffix(".olean")),
                                   str(dependency)], cwd=ROOT / "lean", env=env, stdout=log, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError((out / "dependencies.log").read_text())
        stamp.write_text(fingerprint)
    else:
        print("Reusing unchanged compiled shared dependencies", flush=True)
    env["LEAN_PATH"] = str(out) + os.pathsep + env.get("LEAN_PATH", "")

    def check(item):
        index, file, source = item
        name = f"{index:03}-{file.stem}"
        path, log = out / (name + ".lean"), out / (name + ".log")
        path.write_text(re.sub(r"^import QSym$", "import ExportDependencies\nimport QSym.RationalCertificate", source, flags=re.M))
        started = time.perf_counter()
        try:
            with log.open("w") as stream:
                process = subprocess.Popen(command + [str(path)], cwd=ROOT / "lean", env=env,
                    stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    status = process.wait(timeout=args.timeout)
                except BaseException:
                    # Lake spawns Lean. Killing only Lake leaves a checker alive
                    # and contaminates all subsequent timings.
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    process.wait()
                    raise
        except subprocess.TimeoutExpired:
            status = "timeout"
        if file.read_text() != source:
            raise RuntimeError(f"certificate changed during checking: {file}")
        row = {"file": str(file.relative_to(ROOT) if file.is_absolute() and ROOT in file.parents else file), "status": status,
               "seconds": round(time.perf_counter()-started, 3), "bytes": len(source.encode())}
        print(json.dumps(row), flush=True)
        return row

    items = list((i, f, s) for i, (f, s) in enumerate(zip(files, texts)))
    if args.jobs == 1:
        rows = [check(item) for item in items]
    else:
        with ThreadPoolExecutor(max_workers=args.jobs) as workers:
            rows = list(workers.map(check, items))
    (out / "timings.json").write_text(json.dumps({"jobs": args.jobs, "dependencies": len(needed), "checks": rows}, indent=2))
    return int(any(r["status"] != 0 for r in rows))


if __name__ == "__main__":
    raise SystemExit(main())
