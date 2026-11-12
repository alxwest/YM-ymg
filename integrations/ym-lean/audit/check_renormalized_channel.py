#!/usr/bin/env python3
"""Check the renormalized Gaussian channel against unchanged native imports.

This is a trusted-source workflow. Success does not certify a generated
physical YM mixing coefficient, a complete changed prescription, or existence.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys

from check_requirement_audit import DRIVER, audit_log

HERE = Path(__file__).resolve().parent
AUDITS = {
    "CurvatureVariance.lean": ("YMYMG.CurvatureVariance.", {
        "regulator_product", "regulator_integrable", "regulator_integral",
        "weight_bounds", "weight_sum", "covariance_weight", "weighted_integrable",
        "square_permutation", "weighted_integral_eq", "weighted_integral",
        "curvature_variance", "curvature_integrand", "curvature_integrable",
        "native_curvature_variance",
    }),
    "RenormalizedGaussianChannel.lean": ("YMYMG.RenormalizedGaussian.", {
        "colorSquare_derivative", "halfLaplacian_square", "halfLaplacian_four",
        "subtraction_boundary", "quarticShift_flow", "quarticShift_ir",
        "variance_subtraction", "quarticShift_unique", "subtraction_scale_derivative",
        "gaussianGamma_nonzero", "corrected_lower_coefficient", "corrected_gamma",
        "one_loop_graph_count",
    }),
    "RenormalizedSectorPairing.lean": ("YMYMG.GaussianSector.", {
        "heat3", "heat2", "heat_overlap", "heat_composition", "sum_one_tuple",
        "full_pairing", "small_pairing", "sector_difference", "difference_nonzero",
        "finite_gaussian_cancellation",
    }),
    "QuantumClosureShift.lean": ("YMYMG.QuantumShift.", {
        "wardMap_apply", "tree_closed_all", "one_loop_closed", "shiftedOne_graph_grading",
        "shiftedOne_support", "closed_all", "shifted_tree", "shifted_closed",
        "shifted_graph_grading", "shifted_support",
    }),
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ym-lean", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path,
                        help="New evidence directory; existing results are not overwritten")
    args = parser.parse_args()
    root, out = args.ym_lean.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, LEAN_NUM_THREADS="3")
    sources = [HERE/name for name in AUDITS] + [HERE/name for name in (
        "independent_renormalized.py", "check_renormalized_channel.py",
        "check_requirement_audit.py", "test_requirement_audit.py")]
    sources += [HERE.parent/"verify_existence.py", HERE.parent/"pin.json"]
    hashes = {str(path.relative_to(HERE.parent)): DRIVER.digest(path) for path in sources}
    report = {
        "status": "RENORMALIZED_CHANNEL_AUDIT_FAILED",
        "scope": "Native free curvature integral, subtracted Gaussian channel, conditional sector comparison, and Ward-preserving shifts",
        "existence_only_kernel_certificate": False,
        "full_generated_countermodel_constructed": False,
        "generated_physical_mixing_coefficient_computed": False,
        "complete_changed_prescription_constructed": False,
        "necessity_of_full_native_target_established": False,
        "native_existence_verifier_rerun": False,
        "verifier_revision": DRIVER.PIN["revision"],
        "input_sha256": hashes,
        "checks": [],
    }
    code = 1
    try:
        DRIVER.check_pin(root, env)
        for name, (namespace, declarations) in AUDITS.items():
            command = ["lake", "env", "lean", "-DwarningAsError=true", str(HERE/name)]
            result = subprocess.run(command, cwd=root, env=env, text=True,
                                    capture_output=True, timeout=180)
            log = result.stdout+result.stderr
            (out/(Path(name).stem+".log")).write_text(log, encoding="utf-8")
            check = {"source": name, "command": command, "exit_code": result.returncode}
            report["checks"].append(check)
            if result.returncode != 0:
                raise RuntimeError("Lean compilation failed: "+name)
            check["axioms"] = audit_log(log, {namespace+d for d in declarations})
        for script, log_name in (("test_requirement_audit.py", "audit-log-controls.log"),
                                 ("independent_renormalized.py", "independent.log")):
            result = subprocess.run([sys.executable, str(HERE/script)], cwd=root,
                                    env=env, text=True, capture_output=True, timeout=30)
            (out/log_name).write_text(result.stdout+result.stderr, encoding="utf-8")
            if result.returncode != 0:
                raise RuntimeError("Supplementary check failed: "+script)
            if script == "independent_renormalized.py":
                report["independent"] = json.loads(result.stdout)
                if report["independent"].get("status") != "INDEPENDENT_RENORMALIZED_GAUSSIAN_CHECKS_PASSED":
                    raise RuntimeError("Independent check did not report success")
        DRIVER.check_pin(root, env)
        if hashes != {str(path.relative_to(HERE.parent)): DRIVER.digest(path) for path in sources}:
            raise RuntimeError("Audit inputs changed during the run")
        report.update(status="SCOPED_RENORMALIZED_CHANNEL_CHECKED",
                      trusted_checkout_unchanged=True,
                      audited_declarations=sum(len(ds) for _, ds in AUDITS.values()),
                      native_finite_cutoff_covariance_computed=True,
                      subtracted_gaussian_channel_computed=True,
                      all_loop_ward_shift_checked=True,
                      audit_log_control_tests=5)
        code = 0
    except (OSError, RuntimeError, subprocess.SubprocessError, ValueError) as error:
        report["error"] = str(error)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (out/"result.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in (
        "status", "scope", "existence_only_kernel_certificate",
        "generated_physical_mixing_coefficient_computed", "complete_changed_prescription_constructed",
        "necessity_of_full_native_target_established")}, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
