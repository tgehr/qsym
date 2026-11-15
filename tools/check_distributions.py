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
    imports = ["Binding", "DistributionIntegral", "DistributionModelBridge", "Refinement", "ProofCache", "AxiomCheck", "Numeric", "Tensor", "AC", "Bag"]
    parts = ["\n".join("import QSym." + m for m in imports),
             "import Mathlib.Data.Multiset.Fold\nnamespace QSym.Generated",
             "\n\n".join(blocks[n] for n in blocks if n in needed), "end QSym.Generated"]
    for source in (replay, region):
        parts.append(re.sub(r"^import [^\n]*\n", "", source, flags=re.M))
    for i, (file, source) in enumerate(zip(files, texts)):
        if re.search(r"\b(sorry|admit|native_decide)\b", source):
            raise RuntimeError("unchecked proof in " + str(file))
        source = source.replace("import QSym\n", "")
        namespaces = set(re.findall(r"^namespace (QSym\.[^\n]+)", source, re.M))
        for name in sorted(namespaces, key=len, reverse=True):
            source = source.replace(name, f"QSym.DistributionCheck{i}." + name[5:])
        parts.append("-- " + file.name + "\n" + source)
    return "\n".join(parts), len(needed)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    files = sorted((ROOT / "build/distributions").glob("*.lean"))
    if not files:
        raise RuntimeError("run build/distribution-tests first")
    source, count = batch(files)
    output = ROOT / "build/DistributionCertificates.lean"
    output.write_text(source)
    env = os.environ.copy()
    env.pop("QSYM_PROOF_CACHE", None)
    command = [args.lake, "env", "lean", "-s", "65536"]
    log = ROOT / "build/distribution-check.log"
    with log.open("w") as stream:
        result = subprocess.run(command + [str(output)], cwd=ROOT / "lean", env=env,
                                stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        print(log.read_text())
        return result.returncode
    print(f"Kernel-checked {len(files)} distribution certificates and {count} scalar dependencies.")
    subprocess.run(command + [str(ROOT / "tests/Distributions.lean")],
                   cwd=ROOT / "lean", env=env, check=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
