#!/usr/bin/env python3
"""Kernel-check distribution certificates and their exact source dependencies.

This focused check avoids elaborating unrelated rules in Generated.lean. It
copies the referenced scalar rules and Replay/Region source verbatim, and never
supplies axioms or substitutes native results for proofs. The normal full
verification path continues to check the original certificates importing QSym.
"""
import argparse
import os
from pathlib import Path
import re
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from export_audit import audit_export

ROOT = Path(__file__).resolve().parents[1]


def batch(files):
    replay = (ROOT / "lean/QSym/Replay.lean").read_text()
    region = (ROOT / "lean/QSym/Region.lean").read_text()
    texts = [p.read_text() for p in files]
    needed = set(re.findall(r"Generated\.(r_\w+)", "\n".join(texts + [replay, region])))
    generated = (ROOT / "lean/QSym/Generated.lean").read_text()
    blocks = {name: text for text, name in re.findall(
        r"^(theorem (r_\w+)\b.*?^#qsym_check_axioms \2\b)", generated, re.M | re.S)}
    missing = needed - blocks.keys()
    if missing:
        raise RuntimeError(f"missing scalar dependencies: {sorted(missing)}")
    imports = ["Binding", "DistributionIntegral", "DistributionFibreCertificate", "DistributionGraphBridge", "DistributionMixture", "DistributionSum", "DistributionPolynomialGrid", "Refinement", "ProofCache", "AxiomCheck", "Numeric", "RawPolynomial", "Tensor", "SummationMasks", "AC", "Bag"]
    parts = ["\n".join("import QSym." + m for m in imports),
             "import Mathlib.Data.Multiset.Fold\nnamespace QSym.Generated",
             "\n\n".join(blocks[n] for n in blocks if n in needed), "end QSym.Generated"]
    for source in (replay, region):
        parts.append(re.sub(r"^import [^\n]*\n", "", source, flags=re.M))
    for i, (file, source) in enumerate(zip(files, texts)):
        audit_export(source, str(file))
        source = source.replace("import QSym\n", "")
        namespaces = set(re.findall(r"^namespace (QSym\.[^\n]+)", source, re.M))
        for name in sorted(namespaces, key=len, reverse=True):
            source = source.replace(name, f"QSym.DistributionCheck{i}." + name[5:])
        parts.append("-- " + file.name + "\n" + source)
    return "\n".join(parts), len(needed)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--timing", action="store_true", help="report checking time, excluding shared dependency compilation")
    parser.add_argument("--jobs", type=int, default=1, help="independent Lean checking processes (default: 1)")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    files = sorted((ROOT / "build/distributions").glob("*.lean"))
    if not files:
        raise RuntimeError("run build/distribution-tests first")
    source, count = batch(files)
    offsets = [source.index("-- " + file.name + "\n") for file in files] + [len(source)]
    dependencies = ROOT / "build/DistributionDependencies.lean"
    dependencies.write_text(source[:offsets[0]])
    env = os.environ.copy()
    env.pop("QSYM_PROOF_CACHE", None)
    command = [args.lake, "env", "lean", "-s", "65536"]
    log = ROOT / "build/distribution-check.log"
    with log.open("w") as stream:
        result = subprocess.run(command + ["--root=" + str(ROOT / "build"), "-o",
                               str(dependencies.with_suffix(".olean")), str(dependencies)],
                                cwd=ROOT / "lean", env=env, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        print(log.read_text())
        return result.returncode
    env["LEAN_PATH"] = str(ROOT / "build") + os.pathsep + env.get("LEAN_PATH", "")
    # Bound the accumulated elaborator environment. Each certificate is kept
    # intact; only already compiled shared dependencies cross batch boundaries.
    groups, current, size = [], [], 0
    for a, b in zip(offsets, offsets[1:]):
        text = source[a:b]
        if current and size + len(text.encode()) > 2_000_000:
            groups.append(current)
            current, size = [], 0
        current.append(text)
        size += len(text.encode())
    if current:
        groups.append(current)
    jobs = []
    for i, group in enumerate(groups):
        output = ROOT / f"build/DistributionCertificates{i}.lean"
        output.write_text("import DistributionDependencies\n" + "".join(group))
        jobs.append((output, ROOT / f"build/distribution-check-{i}.log"))

    def check(job):
        output, report = job
        with report.open("w") as stream:
            result = subprocess.run(command + [str(output)], cwd=ROOT / "lean", env=env,
                                    stdout=stream, stderr=subprocess.STDOUT)
        return result.returncode

    started = time.perf_counter()
    with ThreadPoolExecutor(max_workers=args.jobs) as workers:
        statuses = list(workers.map(check, jobs))
    elapsed = time.perf_counter() - started
    with log.open("a") as stream:
        for _, report in jobs:
            stream.write(report.read_text())
    status = next((code for code in statuses if code), 0)
    if status:
        print(log.read_text())
        return status
    print(f"Kernel-checked {len(files)} distribution certificates and {count} scalar dependencies.")
    if args.timing:
        print(f"Export checking: {elapsed:.3f}s, {len(jobs)} batches, {args.jobs} process(es) (includes startup/imports; excludes dependency compilation).")
    subprocess.run(command + [str(ROOT / "tests/Distributions.lean")],
                   cwd=ROOT / "lean", env=env, check=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
