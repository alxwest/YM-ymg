#!/usr/bin/env python3
"""Compile supplementary estimates, then delegate to unchanged ym-lean admission.

Exit 0 ONLY if the native verifier accepts an unconditional exact-target proof.
Exit 2 means no proof was submitted. Exit 1 means rejection/infrastructure error.
Passing the supplementary mathematical lemmas does NOT establish existence.
This is a trusted-code proof workflow, not a sandbox for hostile Lean programs.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PIN = json.loads((HERE / "pin.json").read_text())
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DECLARATIONS = {
    "YMYMG.Existence.remainder_bound_of_limits",
    "YMYMG.Existence.all_orders_of_uniform_regulated_estimates",
    "YMYMG.Existence.RegulatedExpansion.continuum",
    "YMYMG.Existence.allOrderMultiMatch_of_regulated",
    "YMYMG.Existence.allOrderVacuumWordMatch_of_regulated",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def capture(command: list[str], cwd: Path, env: dict[str, str]) -> str:
    return subprocess.check_output(command, cwd=cwd, env=env, text=True).strip()


def check_pin(root: Path, env: dict[str, str]) -> None:
    if capture(["git", "rev-parse", "HEAD"], root, env) != PIN["revision"]:
        raise RuntimeError("Wrong verifier revision; use the pinned trusted checkout")
    if capture(["git", "status", "--porcelain", "--untracked-files=no"], root, env):
        raise RuntimeError("Verifier has tracked changes; refusing to certify against it")
    if (root / "lean-toolchain").read_text().strip() != PIN["lean_toolchain"]:
        raise RuntimeError("Unexpected Lean toolchain")
    for name, expected in PIN["sha256"].items():
        if digest(root / name) != expected:
            raise RuntimeError("Changed trusted verifier file: " + name)


def native_accepted(report: dict, code: int, theorem: str | None) -> bool:
    return (
        code == 0 and theorem is not None
        and report.get("status") == "EXISTENCE_ONLY_KERNEL_PROOF_ACCEPTED"
        and report.get("admitted_target") == PIN["target"]
        and report.get("existence_only_kernel_certificate") is True
        and report.get("kernel_verification_status") == "passed_declared_existence_only_target"
        and report.get("verified_theorem") == theorem
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ym-lean", type=Path, required=True)
    parser.add_argument("--proof-file", type=Path)
    parser.add_argument("--theorem")
    parser.add_argument("--threads", type=int, default=3)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if (args.proof_file is None) != (args.theorem is None):
        parser.error("--proof-file and --theorem must be provided together")
    if args.threads < 1:
        parser.error("--threads must be positive")
    root = args.ym_lean.resolve()
    out = args.out or HERE / "runs" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    out = out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, LEAN_NUM_THREADS=str(args.threads))
    summary = {
        "status": "NOT_ACCEPTED", "existence_only_kernel_certificate": False,
        "supplementary_lemmas_verified": False, "target": PIN["target"],
        "verifier_revision": PIN["revision"], "input_sha256": {},
        "scope": "Exact existence-only admission; no mass-gap claim",
        "commands": [],
    }

    def run(command: list[str], name: str, run_env=None):
        completed = subprocess.run(command, cwd=root, env=run_env or env,
                                   text=True, capture_output=True, timeout=1200)
        (out / (name + ".log")).write_text(completed.stdout + completed.stderr)
        summary["commands"].append({"command": command, "exit_code": completed.returncode})
        return completed

    code = 1
    try:
        check_pin(root, env)
        for name in ["UniformPerturbativeLimit.lean", "UniformPerturbativeLimitAudit.lean"]:
            summary["input_sha256"][name] = digest(HERE / name)
        build = run(["lake", "build", "YangMills.ExistenceOnly"], "target-build")
        if build.returncode:
            raise RuntimeError("Pinned target failed to build")
        lean = capture(["lake", "env", "which", "lean"], root, env)
        lean_path = capture(["lake", "env", "printenv", "LEAN_PATH"], root, env)
        with tempfile.TemporaryDirectory(prefix="ymymg-admission-", dir=root / ".lake") as temp:
            local_env = dict(env, LEAN_PATH=temp + os.pathsep + lean_path)
            compiled = run([lean, "-R", str(HERE), "-DwarningAsError=true", "-o",
                            str(Path(temp) / "UniformPerturbativeLimit.olean"),
                            str(HERE / "UniformPerturbativeLimit.lean")], "support", local_env)
            if compiled.returncode:
                raise RuntimeError("Supplementary limit-passage proof did not compile")
            audited = run([lean, "-R", str(HERE), "-DwarningAsError=true",
                           str(HERE / "UniformPerturbativeLimitAudit.lean")], "support-audit", local_env)
            if audited.returncode:
                raise RuntimeError("Supplementary audit did not compile")
            matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audited.stdout)
            axioms = {name: sorted(x.strip() for x in names.split(",") if x.strip())
                      for name, names in matches}
            if set(axioms) != DECLARATIONS or any(set(xs) - ALLOWED for xs in axioms.values()):
                raise RuntimeError("Missing, unexpected, or unapproved supplementary axiom report")
            summary["supplementary_lemmas_verified"] = True
            summary["supplementary_axioms"] = axioms
        command = [sys.executable, str(root / "scripts/verify_submission.py"),
                   "--claim", "existence", "--report", str(out / "native.json")]
        if args.proof_file is not None:
            proof = args.proof_file.resolve()
            summary["proof_sha256"] = digest(proof)
            command += ["--proof-file", str(proof), "--theorem", args.theorem]
        result = run(command, "native-verifier")
        report = json.loads((out / "native.json").read_text())
        check_pin(root, env)
        accepted = native_accepted(report, result.returncode, args.theorem)
        summary.update(
            status=report.get("status", "VERIFIER_ERROR"),
            existence_only_kernel_certificate=accepted,
            native_exit_code=result.returncode,
            native_summary={k: report.get(k) for k in (
                "status", "admitted_target", "existence_only_shape_status",
                "existence_only_kernel_certificate", "kernel_verification_status",
                "kernel_audit_output_tail", "proof_compile_output_tail", "reason", "error")},
        )
        code = 0 if accepted else (2 if result.returncode == 2 else 1)
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        summary.update(status="VERIFIER_ERROR", error=str(error))
    summary["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (out / "result.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": summary["status"],
                      "existence_only_kernel_certificate": summary["existence_only_kernel_certificate"],
                      "supplementary_lemmas_verified": summary["supplementary_lemmas_verified"],
                      "report": str(out / "result.json")}, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
