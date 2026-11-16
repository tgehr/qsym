"""Fail closed on tactic syntax and unchecked escape hatches in exported Lean."""
import re

FORBIDDEN = re.compile(r"\b(by|decreasing_by|sorry|admit|native_decide)\b|\bqsym_\w+%")


def audit_export(source, name="certificate"):
    match = FORBIDDEN.search(source)
    if match:
        raise RuntimeError(f"tactic or unchecked proof in {name}: {match.group()}")
