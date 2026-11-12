#!/usr/bin/env python3
"""Audit transport of a complete existing native scale normalization.

Rebuilds every local dependency, including the primitive, exact insertion,
residual-limit transport and equivalence of normalization existence. This
does not construct an original interacting family or an existence proof.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys

from check_mixing_transport import AUDITS as MIXING_AUDITS
from check_requirement_audit import DRIVER, audit_log

HERE = Path(__file__).resolve().parent
NEW_AUDITS = {
    "ExactInsertionSmoothness.lean": ("YMYMG.ExactTransport.", {
        "characteristic_add", "characteristic_smul", "localST_action_add", "localST_action_smul",
        "actionLinear", "vertices_scalar_smooth", "classicalWard_smooth", "generatedWard_smooth",
        "primitive_coupling_smooth", "primitive_support_at_one", "exactInsertion_fixed_support",
        "exactInsertion_smooth", "family_exactInsertion_smooth",
    }),
    "PrimitiveTransport.lean": ("YMYMG.ExactTransport.", {
        "changePrimitive", "exactFunctional_apply", "exactInsertion_functional",
        "exactInsertion_change_zero", "exactInsertion_change_succ",
    }),
    "ExactLegendreTransport.lean": ("YMYMG.ExactTransport.", {
        "family_exactFlowJet_change", "family_exactGamma_change",
    }),
    "ScaleNormalizationTransport.lean": ("YMYMG.ScaleNormalizationTransport.", {
        "family_residual_change", "family_residual_weak", "changeNormalization",
        "positiveScale_neg", "normalization_exists_iff",
    }),
}
AUDITS = {**MIXING_AUDITS, **NEW_AUDITS}


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
        "check_scale_normalization_transport.py", "check_mixing_transport.py", "check_scale_derivative_transport.py", "check_physical_word_transport.py",
        "check_dictionary_renormalization.py", "check_requirement_audit.py", "test_requirement_audit.py")]
    sources += [HERE.parent/"verify_existence.py", HERE.parent/"pin.json"]
    hashes = {str(path.relative_to(HERE.parent)): DRIVER.digest(path) for path in sources}
    report = {
        "status": "SCALE_NORMALIZATION_TRANSPORT_AUDIT_FAILED",
        "scope": "Complete conditional native scale-normalization transport and equivalence of normalization existence",
        "original_local_ward_flow_family_constructed": False,
        "original_scale_normalization_constructed": False,
        "family_scale_smoothness_requires_existing_normalization_and_smooth_correction": True,
        "transformed_mixing_constructed": False,
        "transformed_mixing_graph_order_checked": False,
        "native_differential_plus_mixing_covariance_checked": False,
        "fixed_output_relabeling_avoids_support_smoothness_assumption": False,
        "transformed_quantum_exact_primitive_constructed": False,
        "complete_composite_residual_transport_proved": False,
        "generated_scale_normalization_transported": False,
        "generated_physical_mixing_coefficient_computed": False,
        "quantum_exact_coupling_smoothness_derived": False,
        "quantum_exact_legendre_transport_checked": False,
        "native_full_residual_limit_transported": False,
        "normalization_existence_equivalent": False,
        "normalization_existence_equivalence_requires_smooth_correction_and_lower_weight_zero": True,
        "generated_coefficient_family_transported": False,
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
        report.update(status="SCOPED_SCALE_NORMALIZATION_TRANSPORT_CHECKED",
                      trusted_checkout_unchanged=True,
                      transformed_quantum_exact_primitive_constructed=True,
                      complete_composite_residual_transport_proved=True,
                      generated_scale_normalization_transported=True,
                      quantum_exact_coupling_smoothness_derived=True,
                      quantum_exact_legendre_transport_checked=True,
                      native_full_residual_limit_transported=True,
                      normalization_existence_equivalent=True,
                      transformed_mixing_constructed=True,
                      transformed_mixing_graph_order_checked=True,
                      native_differential_plus_mixing_covariance_checked=True,
                      fixed_output_relabeling_avoids_support_smoothness_assumption=True,
                      audited_declarations=sum(len(ds) for _, ds in AUDITS.values()),
                      new_audited_declarations=sum(len(ds) for _, ds in NEW_AUDITS.values()),
                      reused_audited_declarations=sum(len(ds) for _, ds in MIXING_AUDITS.values()),
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
