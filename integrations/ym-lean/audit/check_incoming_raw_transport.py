#!/usr/bin/env python3
"""Audit the native incoming extractor, its coupling jets and weak UV limits.

Rebuild every local dependency and the preceding outgoing audit in a fresh
directory. Conditional raw-data transport is not native existence admission.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys

from check_output_coherence import AUDITS as PREVIOUS_AUDITS
from check_requirement_audit import DRIVER, audit_log

HERE = Path(__file__).resolve().parent
NEW_AUDITS = {
    "IncomingExpansionAlgebra.lean": ("YMYMG.IncomingExpansion.", {
        "expand_natural", "expand_zero", "expand_add", "expand_smul", "expand_transfer",
        "loopDelay", "loopDelay_zero", "loopDelay_succ", "jetDelay", "jetDelay_apply",
    }),
    "IncomingFiniteTransport.lean": ("YMYMG.IncomingExpansion.", {
        "coefficientFunctional_apply", "finiteSlot", "finiteSlot_apply", "finiteSlot_delay",
        "finiteSlot_change", "finiteWord_delay", "finiteWord_native", "finiteWord_change",
    }),
    "IncomingTaylorTransport.lean": ("YMYMG.IncomingExpansion.", {
        "finiteTransform_zero", "finiteTransform_succ", "finiteTransform_smooth",
        "finiteTransform_graph", "finiteTransform_jet",
    }),
    "IncomingNativeExtractor.lean": ("YMYMG.IncomingExpansion.", {
        "evaluateState", "evaluateState_delay", "finiteWord_change_value", "nativeTuple_word",
        "nativeTuple_change", "nativeTuple_smooth", "nativeTuple_changed_smooth",
        "nativeTuple_changed_graph", "tupleJet_eq_jet", "tupleJet_change",
    }),
    "IncomingWeakLimits.lean": ("YMYMG.IncomingExpansion.", {
        "expand_integrable", "expand_integral", "expand_tendsto", "expand_mul",
    }),
    "IncomingNativeLimits.lean": ("YMYMG.IncomingExpansion.", {
        "tupleJet_test_change", "tupleJet_test_integrable", "regularity_change",
        "tupleJet_integral_change", "tupleJet_limit_change",
    }),
    "GeneratedIncomingRaw.lean": ("YMYMG.GeneratedIncomingRaw.", {
        "evaluateJets", "evaluateJets_delay", "expand_distribution_apply", "local_zero",
        "local_add", "local_smul", "expand_local", "incomingRaw_apply", "incomingRaw_local",
        "incomingRaw_limit",
    }),
    "IncomingExpansionInverse.lean": ("YMYMG.IncomingExpansion.", {
        "expand_weight_zero", "expand_shift", "expand_inverse", "regularity_change_iff",
    }),
}
AUDITS = {**PREVIOUS_AUDITS, **NEW_AUDITS}


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
        "check_incoming_raw_transport.py", "check_output_coherence.py", "check_output_recovery.py",
        "check_dictionary_renormalization.py", "check_requirement_audit.py",
        "test_requirement_audit.py")]
    sources += [HERE.parent/"verify_existence.py", HERE.parent/"pin.json"]
    hashes = {str(path.relative_to(HERE.parent)): DRIVER.digest(path) for path in sources}
    report = {
        "status": "INCOMING_RAW_TRANSPORT_AUDIT_FAILED",
        "scope": "Conditional native incoming finite extraction, coupling jets, regularity and local weak-UV raw limits",
        "actual_finite_incoming_expansion_proved": False,
        "anchored_last_insertion_included": False,
        "actual_coupling_jet_transport_proved": False,
        "native_coupling_smoothness_preserved": False,
        "native_graph_grading_preserved": False,
        "native_test_integrability_preserved": False,
        "native_regularity_structure_transported": False,
        "incoming_generated_raw_limits_transported": False,
        "single_distribution_valued_raw_table_constructed": False,
        "incoming_raw_locality_preserved": False,
        "incoming_expansion_inverse_when_lower_weight_zero": False,
        "native_regularity_equivalent_when_lower_weight_zero": False,
        "requires_existing_native_regularities_and_raw_limits": True,
        "raw_table_requires_lower_label_in_basis": True,
        "incoming_transport_requires_equal_engineering_degree": False,
        "infinite_sum_limit_interchange_used": False,
        "combined_incoming_outgoing_physical_recovery_transported": False,
        "full_generated_data_compatibility_constructed": False,
        "generated_coefficient_family_transported": False,
        "original_local_ward_flow_family_constructed": False,
        "all_orders_continuum_matching_proved": False,
        "physical_reconstruction_transported": False,
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
        report.update(status="SCOPED_INCOMING_RAW_TRANSPORT_CHECKED",
                      trusted_checkout_unchanged=True,
                      actual_finite_incoming_expansion_proved=True,
                      anchored_last_insertion_included=True,
                      actual_coupling_jet_transport_proved=True,
                      native_coupling_smoothness_preserved=True,
                      native_graph_grading_preserved=True,
                      native_test_integrability_preserved=True,
                      native_regularity_structure_transported=True,
                      incoming_generated_raw_limits_transported=True,
                      single_distribution_valued_raw_table_constructed=True,
                      incoming_raw_locality_preserved=True,
                      incoming_expansion_inverse_when_lower_weight_zero=True,
                      native_regularity_equivalent_when_lower_weight_zero=True,
                      audited_declarations=sum(len(ds) for _, ds in AUDITS.values()),
                      new_audited_declarations=sum(len(ds) for _, ds in NEW_AUDITS.values()),
                      reused_audited_declarations=sum(len(ds) for _, ds in PREVIOUS_AUDITS.values()),
                      audit_log_control_tests=5)
        code = 0
    except (OSError, RuntimeError, subprocess.SubprocessError, ValueError) as error:
        report["error"] = str(error)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (out/"result.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in (
        "status", "scope", "native_regularity_structure_transported",
        "incoming_generated_raw_limits_transported", "full_generated_data_compatibility_constructed",
        "existence_only_kernel_certificate")}, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
