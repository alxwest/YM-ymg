#!/usr/bin/env python3
"""Audit native exact remainders and coherent equal-degree outgoing transport.

All local dependencies are rebuilt. This checks conditional outgoing data
transport and low-cutoff obstruction criteria, not a native existence proof.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys

from check_output_recovery import AUDITS as RECOVERY_AUDITS
from check_requirement_audit import DRIVER, audit_log

HERE = Path(__file__).resolve().parent
NEW_AUDITS = {
    "OutputRecoveryExact.lean": ("YMYMG.OutputRecoveryExact.", {
        "supported_zero", "supported_sub", "quantumExact_sub", "rawOutput_sub",
        "exactOutput_sub", "exactOutput_zero", "recovery_iff_exact",
        "recovery_of_equal_outputs", "corrected_recovery_iff_exact",
        "no_recovery_of_separating_test",
    }),
    "OutputRecoveryLowCutoff.lean": ("YMYMG.OutputRecoveryLowCutoff.", {
        "monomial_dimension_zero", "primitiveSet_empty", "supportedPrimitive_zero",
        "quantumExact_low_zero", "exactOutput_low_zero", "exact_change_iff_equal_outputs",
        "recovery_low_equation", "recovery_low_iff", "no_low_recovery",
        "antighost_primitive_at_three",
    }),
    "OutputRecoveryCoherent.lean": ("YMYMG.OutputRecoveryCoherent.", {
        "coordinateCorrection_graph", "coordinateCorrection_inverse", "weightedOn_coordinate",
        "correction_enumerated_active", "correction_enumerated_inactive",
        "weights_enumerated_inactive", "sector_recovery", "same_degree_joint",
        "outside_window_joint", "coherent_recovery_of_joint", "coherent_recovery_same_degree",
        "coherent_recovery_same_degree_iff", "coordinateDirectionLE", "directionLE_weights",
        "coherent_coordinate_change",
    }),
    "GeneratedOutputTransport.lean": ("YMYMG.GeneratedOutputTransport.", {
        "local_sub_smul", "scaling_sub_smul", "raw_unchanged", "outputs_apply",
        "outputs_graph", "outputs_local", "outputs_scaling", "outputs_recovery",
    }),
}
AUDITS = {**RECOVERY_AUDITS, **NEW_AUDITS}


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
        "check_output_coherence.py", "check_output_recovery.py",
        "check_dictionary_renormalization.py", "check_requirement_audit.py",
        "test_requirement_audit.py")]
    sources += [HERE.parent/"verify_existence.py", HERE.parent/"pin.json"]
    hashes = {str(path.relative_to(HERE.parent)): DRIVER.digest(path) for path in sources}
    report = {
        "status": "OUTPUT_COHERENCE_AUDIT_FAILED",
        "scope": "Native exact-image criterion, low-cutoff remainder obstruction and equal-degree all-cutoff outgoing transport",
        "native_exact_image_criterion_iff_proved": False,
        "native_primitive_space_empty_through_cutoff_two": False,
        "cutoff_three_antighost_control_checked": False,
        "same_degree_recovery_equivalent_for_fixed_raw": False,
        "same_degree_global_outgoing_table_constructed": False,
        "same_degree_physical_recovery_field_transported": False,
        "same_degree_outgoing_graph_order_preserved": False,
        "same_degree_outgoing_locality_preserved": False,
        "same_degree_outgoing_power_counting_preserved": False,
        "requires_existing_recovery_and_distinct_positive_equal_degree_basis_labels": True,
        "outgoing_transport_holds_raw_data_fixed": True,
        "strict_lowering_global_recovery_transported": False,
        "incoming_generated_raw_limits_transported": False,
        "full_generated_data_compatibility_constructed": False,
        "generated_coefficient_family_transported": False,
        "original_local_ward_flow_family_constructed": False,
        "actual_nonzero_same_flow_obstruction_constructed": False,
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
        report.update(status="SCOPED_OUTPUT_COHERENCE_CHECKED",
                      trusted_checkout_unchanged=True,
                      native_exact_image_criterion_iff_proved=True,
                      native_primitive_space_empty_through_cutoff_two=True,
                      cutoff_three_antighost_control_checked=True,
                      same_degree_recovery_equivalent_for_fixed_raw=True,
                      same_degree_global_outgoing_table_constructed=True,
                      same_degree_physical_recovery_field_transported=True,
                      same_degree_outgoing_graph_order_preserved=True,
                      same_degree_outgoing_locality_preserved=True,
                      same_degree_outgoing_power_counting_preserved=True,
                      audited_declarations=sum(len(ds) for _, ds in AUDITS.values()),
                      new_audited_declarations=sum(len(ds) for _, ds in NEW_AUDITS.values()),
                      reused_audited_declarations=sum(len(ds) for _, ds in RECOVERY_AUDITS.values()),
                      audit_log_control_tests=5)
        code = 0
    except (OSError, RuntimeError, subprocess.SubprocessError, ValueError) as error:
        report["error"] = str(error)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (out/"result.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in (
        "status", "scope", "native_exact_image_criterion_iff_proved",
        "same_degree_physical_recovery_field_transported",
        "full_generated_data_compatibility_constructed", "existence_only_kernel_certificate")}, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
