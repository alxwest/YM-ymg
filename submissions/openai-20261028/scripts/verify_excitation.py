#!/usr/bin/env python3
"""Reproduce the supplementary gap-free excitation corollary, not A1-A8.

SPDX-License-Identifier: Apache-2.0
Uses pinned original source and fresh objects for all supplementary checks.
The original global construction and Comparator endpoints are not rebuilt.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = {
    "YangMills.WightmanTheory.hasFieldExcitation_of_centered_nonzero",
    "YangMills.Hierarchy.nonvacuum_of_reconstructed_nonzero_trace",
    "YangMills.selected_nonvacuum_of_positive_trace",
    "YangMills.selected_constructed_word_outside_vacuum",
}
MODULES = [
    "ExcitationFromPublic", "ExcitationFromConstructed",
    "ExcitationFromPublicAudit", "ExcitationFromConstructedAudit",
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--threads", type=int, default=3)
    parser.add_argument("--run-dir", type=Path)
    args = parser.parse_args()
    if args.threads < 1:
        parser.error("--threads must be positive")
    lake = shutil.which(args.lake)
    if lake is None:
        parser.error("Lake not found; put Elan's bin directory on PATH")
    source, checks = ROOT / "submission", ROOT / "checks"
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    run_dir = (args.run_dir or ROOT / "runs" / ("excitation-" + stamp)).resolve()
    run_dir.mkdir(parents=True, exist_ok=False)
    objects = run_dir / "objects"
    objects.mkdir()
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = str(args.threads)
    record = {
        "status": "running", "started_utc": stamp,
        "scope": "Selected-Final positive-trace consequence; no mass gap",
        "global_existence_rebuilt": False, "comparator_run": False,
        "commands": [], "axioms": {},
        "files": {str((checks / (m + ".lean")).relative_to(ROOT)):
                  digest(checks / (m + ".lean")) for m in MODULES},
        "runner_sha256": digest(Path(__file__)),
    }

    def execute(name: str, command: list[str], *, review: bool = False) -> str:
        log = run_dir / (name + ".log")
        with log.open("w") as stream:
            proc = subprocess.run(command, cwd=source, env=env,
                                  stdout=stream, stderr=subprocess.STDOUT)
        record["commands"].append({"command": command,
                                    "returncode": proc.returncode,
                                    "log": log.name})
        text = log.read_text()
        if proc.returncode:
            raise RuntimeError(f"{name} failed; inspect {log}")
        if review and re.search(r"\bwarning:", text):
            raise RuntimeError(f"{name} emitted a warning; inspect {log}")
        return text

    try:
        execute("original-integrity", [sys.executable,
                str(ROOT / "scripts/verify.py"), "integrity"])
        version = execute("lean-version", [lake, "env", "lean", "--version"])
        if "version 4.32.0," not in version:
            raise RuntimeError("Expected the original pinned Lean 4.32.0")
        record["lean_version"] = version.strip()
        # This avoids the unrelated multi-thousand-module HeadlineSpec chain.
        execute("source-dependencies", [lake, "build", "ChallengeSpec",
                "PublicView", "YM.TraceExtension.Sundial.Grand"])
        lean_path = subprocess.check_output(
            [lake, "env", "printenv", "LEAN_PATH"], cwd=source,
            env=env, text=True).strip()
        lean = subprocess.check_output([lake, "env", "which", "lean"],
                                       cwd=source, env=env, text=True).strip()
        # Fresh review objects take precedence over old exploratory builds.
        env["LEAN_PATH"] = str(objects) + os.pathsep + lean_path
        audit_text = ""
        for module in MODULES:
            text = execute(module, [lean, "-R", str(checks),
                "-DautoImplicit=false", "-DwarningAsError=true",
                "-o", str(objects / (module + ".olean")),
                str(checks / (module + ".lean"))], review=True)
            if module.endswith("Audit"):
                audit_text += text + "\n"
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",
                             audit_text, re.S)
        found = {}
        for name, axioms in reports:
            used = {a.strip() for a in axioms.split(",") if a.strip()}
            if not used <= ALLOWED:
                raise RuntimeError(f"Unapproved axioms in {name}: {used - ALLOWED}")
            found[name] = sorted(used)
        if set(found) != TARGETS:
            raise RuntimeError(f"Unexpected axiom-audit coverage: {set(found)}")
        record["axioms"] = found
        execute("original-integrity-after", [sys.executable,
                str(ROOT / "scripts/verify.py"), "integrity"])
        record["status"] = "passed"
    except Exception as exc:
        record["status"] = "failed"
        record["error"] = str(exc)
    finally:
        record["finished_utc"] = datetime.now(timezone.utc).isoformat()
        (run_dir / "result.json").write_text(json.dumps(record, indent=2) + "\n")
        print(f"{record['status'].upper()}: {run_dir / 'result.json'}")
    return 0 if record["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
