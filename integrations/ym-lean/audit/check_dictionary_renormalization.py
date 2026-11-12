#!/usr/bin/env python3
"""Check dictionary and insertion-limit transport against the pinned native target.

This trusted-source audit builds its own dependency modules in a fresh directory.
It does not construct a full LocalWardFlowFamily or certify Yang--Mills existence.
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
# Dependency order is intentional. No pre-existing local .olean is imported.
AUDITS = {
    "QuantumClosureShift.lean": ("YMYMG.QuantumShift.", {
        "wardMap_apply", "tree_closed_all", "one_loop_closed", "shiftedOne_graph_grading",
        "shiftedOne_support", "closed_all", "shifted_tree", "shifted_closed",
        "shifted_graph_grading", "shifted_support",
    }),
    "DictionaryRenormalization.lean": ("YMYMG.DictionaryRenormalization.", {
        "relations_preserved", "finite_grading", "finite_support", "compatible",
        "unit_dimension", "coordinateWeight", "coordinates_basis", "coordinateDirection",
        "coordinate_weight_selected", "coordinate_weight_lower", "exists_higher_coordinate",
        "scaleDirection", "direction_for_pair", "change_fixed_finite", "change_fixed_physical",
        "change_inverse",
    }),
    "CouplingTaylorShift.lean": ("YMYMG.CouplingTaylor.", {
        "jet_add", "jet_const_mul", "jet_mul_square", "convolve_add",
        "convolve_const_mul", "convolve_delay", "map_delay", "delay_tendsto",
    }),
    "DictionaryInsertionTransport.lean": ("YMYMG.DictionaryRenormalization.", {
        "fullWardRestoration", "fullWardRestoration_iff", "limitCompatible",
        "physicalInsertion_value", "ultravioletInsertion_value", "physicalInsertion_change",
        "ultravioletInsertion_change", "finiteValue_change", "finiteIntegrand_change",
        "delayed_integrable", "finiteIntegral_change", "physicalJets_change",
        "physicalJets_outside", "continuumValue_bound", "continuumValue_change",
        "insertionFunctional_apply", "finiteInsertion_zero", "finiteInsertion_succ",
    }),
}


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
        "check_dictionary_renormalization.py", "check_requirement_audit.py",
        "test_requirement_audit.py")]
    sources += [HERE.parent/"verify_existence.py", HERE.parent/"pin.json"]
    hashes = {str(path.relative_to(HERE.parent)): DRIVER.digest(path) for path in sources}
    report = {
        "status": "DICTIONARY_RENORMALIZATION_AUDIT_FAILED",
        "scope": "Global finite dictionary correction, exact inverse, UV/IR insertion limits and full multi-Ward restoration equivalence",
        "existence_only_kernel_certificate": False,
        "complete_local_ward_flow_family_constructed": False,
        "generated_scale_normalization_transported": False,
        "generated_physical_mixing_coefficient_computed": False,
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
        report.update(status="SCOPED_DICTIONARY_RENORMALIZATION_CHECKED",
                      trusted_checkout_unchanged=True,
                      audited_declarations=sum(len(ds) for _, ds in AUDITS.values()),
                      new_audited_declarations=42,
                      reused_audited_declarations=10,
                      dictionary_compatibility_preserved=True,
                      insertion_limit_compatibility_preserved=True,
                      full_multi_ward_restoration_equivalent=True,
                      audit_log_control_tests=5)
        code = 0
    except (OSError, RuntimeError, subprocess.SubprocessError, ValueError) as error:
        report["error"] = str(error)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (out/"result.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in (
        "status", "scope", "existence_only_kernel_certificate",
        "complete_local_ward_flow_family_constructed", "generated_scale_normalization_transported",
        "generated_physical_mixing_coefficient_computed")}, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
