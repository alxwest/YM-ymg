#!/usr/bin/env python3
"""Audit the computed Legendre transform and native CS differential terms.

Rebuilds all local modules against the pinned target. A complete changed
scale normalization, residual cancellation and existence proof remain absent.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys

from check_physical_word_transport import AUDITS as FAMILY_AUDITS
from check_requirement_audit import DRIVER, audit_log

HERE = Path(__file__).resolve().parent
NEW_AUDITS = {
    "TupleJetShift.lean": ("YMYMG.TupleJet.", {
        "allocation_le", "bounded_sum_eq_allocation", "bounded_pair_eq_allocation",
        "allocation_shift_head", "delay_if", "tupleConvolve_delay",
    }),
    "LegendreDictionaryTransport.lean": ("YMYMG.LegendreTransport.", {
        "partitionValue_eq_tuple", "partitionValue_delay", "meanFieldCompose_delay",
        "substitutionSummand_add", "substitutionSummand_smul", "lowerComposition_add",
        "lowerComposition_smul", "lowerComposition_eq_truncate", "truncate_delay",
        "meanFieldCompose_zero", "lowerComposition_delay", "insertion_add", "insertion_smul",
        "insertion_delay", "flowJet_change", "liftedGamma_change", "positiveScale_change",
        "family_liftedGamma_change", "changeFamily_scale_smooth",
    }),
    "ScaleDerivativeTransport.lean": ("YMYMG.ScaleTransport.", {
        "amplitudeDelay_add", "amplitudeDelay_sub", "scalarAction_add", "scalarAction_smul",
        "scalarAction_delay", "fieldAction_add", "fieldAction_smul", "fieldAction_delay",
        "couplingDerivative_add", "couplingDerivative_smul", "couplingDerivative_delay",
        "delay_differentiable", "scaleDerivative_add", "scaleDerivative_smul_delay",
        "compositeResidual_parts", "differentialPart_change", "differentialPart_congr_nhds",
        "family_scale_differentiable", "family_differential_change",
        "beta_correction_four_two", "beta_correction_four_two_ne_zero",
    }),
    "WeakLocalTransport.lean": ("YMYMG.ScaleTransport.", {
        "weakLocal_zero", "weakLocal_add", "weakLocal_smul", "weakLocal_delay",
        "weakLocal_congr_eventually",
    }),
}
AUDITS = {**FAMILY_AUDITS, **NEW_AUDITS}


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
        "check_scale_derivative_transport.py", "check_physical_word_transport.py",
        "check_dictionary_renormalization.py", "check_requirement_audit.py", "test_requirement_audit.py")]
    sources += [HERE.parent/"verify_existence.py", HERE.parent/"pin.json"]
    hashes = {str(path.relative_to(HERE.parent)): DRIVER.digest(path) for path in sources}
    report = {
        "status": "SCALE_DERIVATIVE_TRANSPORT_AUDIT_FAILED",
        "scope": "Actual Legendre-recursion transport, joint scale smoothness, native CS differential product rules and weak residual limit stability",
        "original_local_ward_flow_family_constructed": False,
        "original_scale_normalization_constructed": False,
        "family_scale_smoothness_requires_existing_normalization_and_smooth_correction": True,
        "transformed_mixing_constructed": False,
        "transformed_quantum_exact_primitive_constructed": False,
        "complete_composite_residual_transport_proved": False,
        "generated_scale_normalization_transported": False,
        "generated_physical_mixing_coefficient_computed": False,
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
        report.update(status="SCOPED_SCALE_DERIVATIVE_TRANSPORT_CHECKED",
                      trusted_checkout_unchanged=True,
                      audited_declarations=sum(len(ds) for _, ds in AUDITS.values()),
                      new_audited_declarations=sum(len(ds) for _, ds in NEW_AUDITS.values()),
                      reused_audited_declarations=sum(len(ds) for _, ds in FAMILY_AUDITS.values()),
                      native_legendre_recursion_transport_checked=True,
                      changed_lifted_scale_smoothness_field_checked=True,
                      native_cs_differential_part_transported=True,
                      scale_product_rule_term_retained=True,
                      coupling_product_rule_term_retained=True,
                      beta_correction_nonzero_control_checked=True,
                      weak_residual_linear_limit_stability_checked=True,
                      audit_log_control_tests=5)
        code = 0
    except (OSError, RuntimeError, subprocess.SubprocessError, ValueError) as error:
        report["error"] = str(error)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (out/"result.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in (
        "status", "scope", "existence_only_kernel_certificate",
        "transformed_mixing_constructed", "transformed_quantum_exact_primitive_constructed",
        "complete_composite_residual_transport_proved", "generated_scale_normalization_transported")}, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
