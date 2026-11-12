#!/usr/bin/env python3
"""Audit complete conditional native generated-data and scale-family transport.

This rebuilds the incoming, outgoing, Ward-family and scale-normalization
proofs together. It does not construct their starting Yang--Mills data or
certify the source submission as a proof of native existence.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys

from check_scale_normalization_transport import AUDITS as NORMALIZATION_AUDITS
from check_incoming_raw_transport import AUDITS as INCOMING_AUDITS
from check_requirement_audit import DRIVER, audit_log

HERE = Path(__file__).resolve().parent
BASE_AUDITS = {**NORMALIZATION_AUDITS, **INCOMING_AUDITS}
NEW_AUDITS = {
    "IncomingRecoveryLinear.lean": ("YMYMG.IncomingRecovery.", {
        "vector_delay_apply", "sumConvolve", "sumConvolve_delay", "matrixConvolve",
        "matrixConvolve_delay", "support_delay_generic", "rawFunctional_apply",
        "liftedFunctional_apply", "exactMap", "exactMap_apply", "rawFunctional_delay",
        "liftedFunctional_delay", "exactMap_delay", "supported_add", "supported_smul",
        "supported_delay", "recovery_add", "recovery_smul", "recovery_delay",
    }),
    "IncomingRecoveryCoherent.lean": ("YMYMG.IncomingRecovery.", {
        "lifted_enumeration", "recovery_enumeration", "coherent_add", "coherent_smul",
        "coherent_delay", "expand_recovery",
    }),
    "IncomingPhysicalBounds.lean": ("YMYMG.IncomingPhysicalBounds.", {
        "expand_restrict", "expand_graph", "scaling_zero", "scaling_add", "scaling_smul",
        "clusterInputDegrees_tuple", "incomingPhysical_apply", "incomingPhysical_scaling",
    }),
    "GeneratedDataTransport.lean": ("YMYMG.GeneratedDataTransport.", {
        "evaluateCoordinate", "evaluateCoordinate_delay", "expand_coordinate",
        "inputWeight_degree", "inputWeight_direction", "combined_recovery",
        "compatible_change", "compatible_exists_iff",
    }),
    "GeneratedCoefficientFamilyTransport.lean": ("YMYMG.GeneratedDataTransport.", {
        "coordinate_lower_weight_zero", "changeCoefficientFamily", "coefficientFamily_exists_iff",
        "changeNormalizedData", "normalizedData_exists_iff",
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
        "check_generated_data_transport.py", "check_scale_normalization_transport.py",
        "check_mixing_transport.py", "check_scale_derivative_transport.py",
        "check_physical_word_transport.py", "check_incoming_raw_transport.py",
        "check_output_coherence.py", "check_output_recovery.py",
        "check_dictionary_renormalization.py", "check_requirement_audit.py",
        "test_requirement_audit.py")]
    sources += [HERE.parent/"verify_existence.py", HERE.parent/"pin.json"]
    hashes = {str(path.relative_to(HERE.parent)): DRIVER.digest(path) for path in sources}
    report = {
        "status": "GENERATED_DATA_TRANSPORT_AUDIT_FAILED",
        "scope": "Complete conditional equal-degree native generated-data, coefficient-family and normalization transport",
        "native_exact_primitive_transported_with_raw_and_physical_coefficients": False,
        "recovery_independent_of_active_basis_enumeration": False,
        "incoming_physical_graph_order_preserved": False,
        "incoming_physical_partial_collision_bounds_preserved": False,
        "combined_incoming_outgoing_physical_recovery_transported": False,
        "single_distribution_valued_generated_table_constructed": False,
        "full_generated_data_compatibility_constructed": False,
        "compatible_generated_data_existence_equivalent": False,
        "generated_coefficient_family_transported": False,
        "coefficient_family_existence_equivalent": False,
        "generated_scale_normalization_transported": False,
        "coefficient_and_normalization_witnesses_transported_together": False,
        "coefficient_and_normalization_existence_equivalent": False,
        "requires_distinct_positive_equal_degree_basis_labels": True,
        "requires_existing_native_family_and_coefficient_data": True,
        "normalization_transport_requires_existing_normalization_and_smooth_correction": True,
        "strict_lowering_full_generated_data_transport_proved": False,
        "original_local_ward_flow_family_constructed": False,
        "original_generated_coefficient_family_constructed": False,
        "original_scale_normalization_constructed": False,
        "all_orders_continuum_matching_proved": False,
        "physical_reconstruction_transported": False,
        "complete_existence_targets_equivalent": False,
        "native_target_inconsistency_established": False,
        "necessity_of_full_native_target_established": False,
        "existence_only_kernel_certificate": False,
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
        report.update(status="SCOPED_GENERATED_DATA_TRANSPORT_CHECKED",
                      trusted_checkout_unchanged=True,
                      native_exact_primitive_transported_with_raw_and_physical_coefficients=True,
                      recovery_independent_of_active_basis_enumeration=True,
                      incoming_physical_graph_order_preserved=True,
                      incoming_physical_partial_collision_bounds_preserved=True,
                      combined_incoming_outgoing_physical_recovery_transported=True,
                      single_distribution_valued_generated_table_constructed=True,
                      full_generated_data_compatibility_constructed=True,
                      compatible_generated_data_existence_equivalent=True,
                      generated_coefficient_family_transported=True,
                      coefficient_family_existence_equivalent=True,
                      generated_scale_normalization_transported=True,
                      coefficient_and_normalization_witnesses_transported_together=True,
                      coefficient_and_normalization_existence_equivalent=True,
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
        "status", "scope", "full_generated_data_compatibility_constructed",
        "generated_coefficient_family_transported", "all_orders_continuum_matching_proved",
        "existence_only_kernel_certificate")}, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
