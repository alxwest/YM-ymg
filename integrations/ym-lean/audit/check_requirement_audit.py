#!/usr/bin/env python3
"""Check requirement diagnostics, never certify Yang--Mills existence.

Requires the pinned, unchanged ym-lean checkout and built dependencies.
This is a trusted-source workflow, not a sandbox for hostile Lean input.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("existence_driver", HERE.parent / "verify_existence.py")
assert SPEC is not None and SPEC.loader is not None
DRIVER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(DRIVER)
AUDITS = {
    "BasisConsistency.lean": ("YMYMG.BasisAudit.", {
        "coordinates_symm_single", "conjugate_entry", "conjugate_symm_entry",
        "reindexFrame", "stripping_reindex", "all_orders_reindex", "all_orders_reindex_iff",
    }),
    "KernelCoefficients.lean": ("YMYMG.KernelAudit.", {
        "wick_four_bosons", "wick_four_fermions", "wick_four_equal", "wick_six_equal",
        "bare_four_equal", "bare_six_equal", "wick_normal_four_vacuum",
        "wick_normal_four_two_legs", "normal_four_change", "curvature01_integrand",
        "normalized_lower_output_zero",
    }),
    "CutoffDerivative.lean": ("YMYMG.KernelAudit.", {
        "covarianceAt_eq", "covariance_derivative",
    }),
    "GeneratedOrders.lean": ("YMYMG.GeneratedAudit.", {
        "beta_below_three", "beta_three", "gamma_classical", "gamma_below_two", "gamma_two",
    }),
}


def audit_log(log: str, expected: set[str]) -> dict[str, list[str]]:
    matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
    matches += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    axioms = {name: sorted(a.strip() for a in raw.split(",") if a.strip())
              for name, raw in matches}
    if len(matches) != len(expected) or set(axioms) != expected:
        raise RuntimeError("Missing, duplicate, or unexpected declaration audit")
    if any(set(used) - DRIVER.ALLOWED for used in axioms.values()):
        raise RuntimeError("Unapproved axiom dependency")
    return axioms


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ym-lean", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path,
                        help="New output directory; existing evidence is not overwritten")
    args = parser.parse_args()
    root, out = args.ym_lean.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, LEAN_NUM_THREADS="3")
    sources = [HERE / name for name in AUDITS] + [HERE / "independent_coefficients.py",
              Path(__file__).resolve(), HERE.parent / "verify_existence.py", HERE.parent / "pin.json"]
    hashes = {str(path.relative_to(HERE.parent)): DRIVER.digest(path) for path in sources}
    report = {
        "status": "REQUIREMENT_AUDIT_FAILED",
        "scope": "Label permutations, finite-cutoff kernels, and generated order reductions",
        "existence_only_kernel_certificate": False,
        "full_generated_countermodel_constructed": False,
        "generated_physical_mixing_coefficient_computed": False,
        "necessity_of_full_native_target_established": False,
        "verifier_revision": DRIVER.PIN["revision"],
        "input_sha256": hashes,
        "checks": [],
    }
    code = 1
    try:
        DRIVER.check_pin(root, env)
        for name, (namespace, declarations) in AUDITS.items():
            command = ["lake", "env", "lean", "-DwarningAsError=true", str(HERE / name)]
            result = subprocess.run(command, cwd=root, env=env, text=True,
                                    capture_output=True, timeout=180)
            log = result.stdout + result.stderr
            (out / (Path(name).stem + ".log")).write_text(log, encoding="utf-8")
            check = {"source": name, "command": command, "exit_code": result.returncode}
            report["checks"].append(check)
            if result.returncode != 0:
                raise RuntimeError("Lean compilation failed: " + name)
            check["axioms"] = audit_log(log, {namespace + d for d in declarations})
        command = [sys.executable, str(HERE / "independent_coefficients.py")]
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                capture_output=True, timeout=30)
        (out / "independent.log").write_text(result.stdout + result.stderr, encoding="utf-8")
        if result.returncode != 0:
            raise RuntimeError("Independent coefficient check failed")
        independent = json.loads(result.stdout)
        if independent.get("status") != "INDEPENDENT_GAUSSIAN_CHECKS_PASSED":
            raise RuntimeError("Independent check did not report success")
        report["independent"] = independent
        DRIVER.check_pin(root, env)
        if hashes != {str(path.relative_to(HERE.parent)): DRIVER.digest(path) for path in sources}:
            raise RuntimeError("Audit inputs changed during the run")
        report.update(status="SCOPED_REQUIREMENT_AUDITS_CHECKED",
                      trusted_checkout_unchanged=True,
                      audited_declarations=sum(len(ds) for _, ds in AUDITS.values()))
        code = 0
    except (OSError, RuntimeError, subprocess.SubprocessError, ValueError) as error:
        report["error"] = str(error)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (out / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in (
        "status", "scope", "existence_only_kernel_certificate",
        "full_generated_countermodel_constructed", "generated_physical_mixing_coefficient_computed",
        "necessity_of_full_native_target_established")}, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
