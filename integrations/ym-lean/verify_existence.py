#!/usr/bin/env python3
"""Compile supplementary estimates, then delegate to unchanged ym-lean admission.

Exit 0 ONLY if the native verifier accepts an unconditional exact-target proof.
Exit 2 means no proof was submitted or its signature is incompatible.
Exit 1 means rejection/infrastructure error. --source submits the actual
universe-translated October theorem, after checking its source proof.
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
SPACETIME_DECLARATIONS = {
    "YMYMG.SpacetimeTransport.time_coordinate",
    "YMYMG.SpacetimeTransport.minkowski_square",
    "YMYMG.SpacetimeTransport.forward_cone",
    "YMYMG.SpacetimeTransport.spacelike",
    "YMYMG.SpacetimeTransport.native_source_test",
    "YMYMG.SpacetimeTransport.source_native_test",
}
FINITE_REGULATOR_DECLARATIONS = {
    "YMYMG.FiniteRegulatorTransport.aspiration_has_jet",
    "YMYMG.FiniteRegulatorTransport.finite_wilson_jet",
    "YMYMG.FiniteRegulatorTransport.finite_haar_wilson_jet",
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
    parser.add_argument("--source", action="store_true",
                        help="Stage and submit this checkout's real October source translation")
    parser.add_argument("--threads", type=int, default=3)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if (args.proof_file is None) != (args.theorem is None):
        parser.error("--proof-file and --theorem must be provided together")
    if args.source and args.proof_file is not None:
        parser.error("--source cannot be combined with --proof-file or --theorem")
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
        "source_translation_verified": False, "spacetime_transport_verified": False,
        "finite_regulator_transport_verified": False,
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
        proof_file, theorem = args.proof_file, args.theorem
        modules = [("UniformPerturbativeLimit", DECLARATIONS)]
        source_root = HERE.parents[1]
        source_package = source_root / "submissions/openai-20261028"
        integrity_command = [sys.executable, str(source_package / "scripts/verify.py"), "integrity"]
        if args.source:
            summary["source_revision"] = capture(["git", "rev-parse", "HEAD"], source_root, env)
            integrity = run(integrity_command, "source-integrity-before")
            if integrity.returncode:
                raise RuntimeError("Original source package failed its integrity check")
            env["YM_YMG_ROOT"] = str(source_root)
            translated = run(["bash", str(root / "scripts/translate_ym_ymg.sh")],
                             "source-translation")
            if translated.returncode or "SOURCE_TRANSLATION_CHECKED:" not in translated.stdout:
                raise RuntimeError("Actual source translation failed its build/signature/axiom check")
            summary["source_translation_verified"] = True
            stage = root / ".lake/ym-ymg-integration"
            env["LEAN_PATH"] = os.pathsep.join([
                str(stage / ".lake/build/lib/lean"),
                str(source_package / "submission/.lake/build/lib/lean"),
                env.get("LEAN_PATH", ""),
            ])
            proof_file = stage / "YMGBridge/Solution.lean"
            theorem = "YMGBridge.jointExistence"
            modules.append(("SpacetimeTransport", SPACETIME_DECLARATIONS))
            modules.append(("FiniteRegulatorTransport", FINITE_REGULATOR_DECLARATIONS))
        for name in [name + suffix for name, _ in modules
                     for suffix in (".lean", "Audit.lean")]:
            summary["input_sha256"][name] = digest(HERE / name)
        summary["input_sha256"]["verify_existence.py"] = digest(Path(__file__))
        summary["input_sha256"]["pin.json"] = digest(HERE / "pin.json")
        build = run(["lake", "build", "YangMills.ExistenceOnly"], "target-build")
        if build.returncode:
            raise RuntimeError("Pinned target failed to build")
        lean = capture(["lake", "env", "which", "lean"], root, env)
        lean_path = capture(["lake", "env", "printenv", "LEAN_PATH"], root, env)
        with tempfile.TemporaryDirectory(prefix="ymymg-admission-", dir=root / ".lake") as temp:
            local_env = dict(env, LEAN_PATH=temp + os.pathsep + lean_path)
            axioms = {}
            for module, declarations in modules:
                compiled = run([lean, "-R", str(HERE), "-DwarningAsError=true", "-o",
                                str(Path(temp) / (module + ".olean")),
                                str(HERE / (module + ".lean"))], module, local_env)
                if compiled.returncode:
                    raise RuntimeError("Supplementary proof did not compile: " + module)
                audited = run([lean, "-R", str(HERE), "-DwarningAsError=true",
                               str(HERE / (module + "Audit.lean"))], module + "-audit", local_env)
                if audited.returncode:
                    raise RuntimeError("Supplementary audit did not compile: " + module)
                matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audited.stdout)
                found = {name: sorted(x.strip() for x in names.split(",") if x.strip())
                         for name, names in matches}
                found.update({name: [] for name in re.findall(
                    r"'([^']+)' does not depend on any axioms", audited.stdout)})
                if set(found) != declarations or any(set(xs) - ALLOWED for xs in found.values()):
                    raise RuntimeError("Missing, unexpected, or unapproved axiom report: " + module)
                axioms.update(found)
            summary["supplementary_lemmas_verified"] = True
            summary["supplementary_axioms"] = axioms
            summary["spacetime_transport_verified"] = args.source
            summary["finite_regulator_transport_verified"] = args.source
        command = [sys.executable, str(root / "scripts/verify_submission.py"),
                   "--claim", "existence", "--report", str(out / "native.json")]
        if proof_file is not None:
            proof = proof_file.resolve()
            summary["proof_sha256"] = digest(proof)
            summary["submitted_theorem"] = theorem
            command += ["--proof-file", str(proof), "--theorem", theorem]
        result = run(command, "native-verifier")
        report = json.loads((out / "native.json").read_text())
        check_pin(root, env)
        if args.source:
            integrity = run(integrity_command, "source-integrity-after")
            if integrity.returncode:
                raise RuntimeError("Original source package changed during verification")
        accepted = native_accepted(report, result.returncode, theorem)
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
                      "source_translation_verified": summary["source_translation_verified"],
                      "spacetime_transport_verified": summary["spacetime_transport_verified"],
                      "finite_regulator_transport_verified": summary["finite_regulator_transport_verified"],
                      "report": str(out / "result.json")}, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
