#!/usr/bin/env python3
"""Audit fixed-cutoff native output recovery and coefficient coherence.

Rebuilds the complete local dependency chain in a fresh directory. The
two-label obstruction is an algebraic diagnostic, not a generated Yang--Mills
countermodel or an existence certificate.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys

from check_dictionary_renormalization import AUDITS as DICTIONARY_AUDITS
from check_requirement_audit import DRIVER, audit_log

HERE = Path(__file__).resolve().parent
BASE_AUDITS = {**DICTIONARY_AUDITS,
    "WordJetAlgebra.lean": ("YMYMG.WordJet.", {
        "convolve_comm", "convolve_add_right", "convolve_smul_right",
        "convolve_delay_right", "delayMap", "insertionMap", "insertionMap_delay",
    }),
}
NEW_AUDITS = {
    "OutputCoefficientShear.lean": ("YMYMG.OutputRecovery.", {
        "weighted_corrected", "weighted_convolve", "weighted_delay_convolve",
        "assemble_dictionary_change", "assemble_corrected", "assemble_cancel",
        "corrected_graph_order",
    }),
    "OutputRecoveryTransport.lean": ("YMYMG.OutputRecovery.", {
        "liftedOutput_value", "liftedOutput_corrected", "recovery_corrected",
        "recovery_fixed", "inactive_weights", "recovery_exists_iff",
        "raw_cutoff_difference", "recovery_cutoff_difference",
    }),
    "OutputRecoveryCutoffs.lean": ("YMYMG.OutputRecoveryCutoffs.", {
        "weighted_enumeration", "corrected_enumeration",
        "correction_cutoff_difference", "correction_coherent_iff",
        "unitJet_convolve", "convolve_unitJet", "twoLabel_assemble_low",
        "twoLabel_assemble_high", "simultaneous_iff", "full_recovery",
        "unchanged_recovery", "leading_tail_obstruction", "unit_tail_obstruction",
        "unitJet_graph",
    }),
}
AUDITS = {**BASE_AUDITS, **NEW_AUDITS}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ym-lean", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path,
                        help="Fresh evidence directory; existing files are not overwritten")
    args = parser.parse_args()
    root, out = args.ym_lean.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    build = out/".build"
    build.mkdir()
    env = dict(os.environ, LEAN_NUM_THREADS="3", LEAN_PATH=str(build))
    sources = [HERE/name for name in AUDITS] + [HERE/name for name in (
        "check_output_recovery.py", "check_dictionary_renormalization.py",
        "check_requirement_audit.py", "test_requirement_audit.py")]
    sources += [HERE.parent/"verify_existence.py", HERE.parent/"pin.json"]
    hashes = {str(path.relative_to(HERE.parent)): DRIVER.digest(path) for path in sources}
    report = {
        "status": "OUTPUT_RECOVERY_AUDIT_FAILED",
        "scope": "Conditional fixed-cutoff native output recovery, exact coefficient coherence criterion and two-label obstruction",
        "fixed_cutoff_native_recovery_transport_proved": False,
        "fixed_cutoff_recovery_existence_equivalent": False,
        "fixed_cutoff_raw_vector_held_fixed": True,
        "cutoff_coherence_criterion_proved": False,
        "two_label_shared_coefficients_obstruction_proved": False,
        "native_generated_exact_remainders_retained": False,
        "native_raw_cutoff_difference_checked": False,
        "native_recovery_cross_cutoff_identity_checked": False,
        "incoming_generated_raw_limits_transported": False,
        "generated_coefficient_family_transported": False,
        "original_local_ward_flow_family_constructed": False,
        "same_flow_nonzero_tail_constructed": False,
        "full_generated_countermodel_constructed": False,
        "native_target_inconsistency_established": False,
        "physical_reconstruction_transported": False,
        "existence_only_kernel_certificate": False,
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
            artifact = build/(Path(name).stem+".olean")
            command = ["lake", "env", "lean", "-R", str(HERE), "-DwarningAsError=true",
                       "-o", str(artifact), str(HERE/name)]
            result = subprocess.run(command, cwd=root, env=env, text=True,
                                    capture_output=True, timeout=180)
            log = result.stdout+result.stderr
            (out/(Path(name).stem+".log")).write_text(log, encoding="utf-8")
            check = {"source": name, "command": command, "exit_code": result.returncode}
            report["checks"].append(check)
            if result.returncode != 0:
                raise RuntimeError("Lean compilation failed: "+name)
            check["axioms"] = audit_log(log, {namespace+d for d in declarations})
            if not artifact.is_file():
                raise RuntimeError("Missing compiled module: "+name)
            check["compiled_module_sha256"] = DRIVER.digest(artifact)
        result = subprocess.run([sys.executable, str(HERE/"test_requirement_audit.py")],
                                cwd=root, env=env, text=True, capture_output=True, timeout=30)
        (out/"audit-log-controls.log").write_text(result.stdout+result.stderr, encoding="utf-8")
        if result.returncode != 0:
            raise RuntimeError("Audit-log controls failed")
        DRIVER.check_pin(root, env)
        if hashes != {str(path.relative_to(HERE.parent)): DRIVER.digest(path) for path in sources}:
            raise RuntimeError("Audit inputs changed during the run")
        report.update(status="SCOPED_OUTPUT_RECOVERY_CHECKED",
                      trusted_checkout_unchanged=True,
                      fixed_cutoff_native_recovery_transport_proved=True,
                      fixed_cutoff_recovery_existence_equivalent=True,
                      cutoff_coherence_criterion_proved=True,
                      two_label_shared_coefficients_obstruction_proved=True,
                      native_generated_exact_remainders_retained=True,
                      native_raw_cutoff_difference_checked=True,
                      native_recovery_cross_cutoff_identity_checked=True,
                      audited_declarations=sum(len(ds) for _, ds in AUDITS.values()),
                      new_audited_declarations=sum(len(ds) for _, ds in NEW_AUDITS.values()),
                      reused_audited_declarations=sum(len(ds) for _, ds in BASE_AUDITS.values()),
                      audit_log_control_tests=5)
        code = 0
    except (OSError, RuntimeError, subprocess.SubprocessError, ValueError) as error:
        report["error"] = str(error)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (out/"result.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in (
        "status", "scope", "fixed_cutoff_native_recovery_transport_proved",
        "cutoff_coherence_criterion_proved", "generated_coefficient_family_transported",
        "existence_only_kernel_certificate")}, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
