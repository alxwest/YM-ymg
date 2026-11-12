#!/usr/bin/env python3
"""Check transport of native physical words and a complete existing Ward family.

Builds all local modules afresh against the pinned, unchanged native target.
This is a conditional family equivalence, not a Yang--Mills existence proof.
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
NEW_AUDITS = {
    "WordJetAlgebra.lean": ("YMYMG.WordJet.", {
        "convolve_comm", "convolve_add_right", "convolve_smul_right",
        "convolve_delay_right", "delayMap", "insertionMap", "insertionMap_delay",
    }),
    "PhysicalWordTransport.lean": ("YMYMG.DictionaryRenormalization.", {
        "slotMap_delay", "slotMap_change", "wordMap_append", "wordMap_delay",
        "wordMap_change_head", "wordMap_transfer", "labels_of_slots", "wordMap_native",
        "exactWordMap_delay", "exactWordMap_native", "delay_preserves_graph",
        "delay_preserves_zero", "physical_word_graph", "physical_word_null",
        "physical_word_null_iff", "physical_word_graph_iff", "changeFamily",
        "changeFamily_inverse", "changeFamilyEquiv",
    }),
    "ChangedFamilyLegendre.lean": ("YMYMG.DictionaryRenormalization.", {
        "changeFamily_lift_directional", "changeFamily_exact_directional",
    }),
}
# The inherited order followed by these modules is the dependency order.
AUDITS = {**DICTIONARY_AUDITS, **NEW_AUDITS}


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
        "check_physical_word_transport.py", "check_dictionary_renormalization.py",
        "check_requirement_audit.py", "test_requirement_audit.py")]
    sources += [HERE.parent/"verify_existence.py", HERE.parent/"pin.json"]
    hashes = {str(path.relative_to(HERE.parent)): DRIVER.digest(path) for path in sources}
    report = {
        "status": "PHYSICAL_WORD_TRANSPORT_AUDIT_FAILED",
        "scope": "Invariant physical words, invertible transport of a complete existing Ward family, and two conditional directional-Legendre fields",
        "existing_local_ward_flow_family_required": True,
        "original_local_ward_flow_family_constructed": False,
        "directional_transport_requires_existing_scale_normalization": True,
        "original_scale_normalization_constructed": False,
        "existence_only_kernel_certificate": False,
        "generated_scale_normalization_transported": False,
        "generated_coefficient_family_transported": False,
        "physical_reconstruction_transported": False,
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
        report.update(status="SCOPED_PHYSICAL_WORD_TRANSPORT_CHECKED",
                      trusted_checkout_unchanged=True,
                      audited_declarations=sum(len(ds) for _, ds in AUDITS.values()),
                      new_audited_declarations=sum(len(ds) for _, ds in NEW_AUDITS.values()),
                      reused_audited_declarations=sum(len(ds) for _, ds in DICTIONARY_AUDITS.values()),
                      physical_state_null_identity_equivalent=True,
                      physical_word_graph_order_equivalent=True,
                      complete_local_ward_flow_family_transported=True,
                      family_change_invertible_if_lower_weight_zero=True,
                      changed_lift_directional_field_checked=True,
                      changed_exact_directional_field_checked=True,
                      audit_log_control_tests=5)
        code = 0
    except (OSError, RuntimeError, subprocess.SubprocessError, ValueError) as error:
        report["error"] = str(error)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (out/"result.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in (
        "status", "scope", "existing_local_ward_flow_family_required",
        "original_local_ward_flow_family_constructed", "existence_only_kernel_certificate",
        "generated_scale_normalization_transported")}, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
