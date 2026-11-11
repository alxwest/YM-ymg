#!/usr/bin/env python3
"""Check the finite-sector diagnostic, NOT Yang--Mills existence admission.

Requires the unchanged pinned ym-lean checkout and its built dependencies.
This is a trusted-source audit runner, not a sandbox for hostile Lean input.
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

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("existence_driver", HERE.parent / "verify_existence.py")
assert SPEC is not None and SPEC.loader is not None
DRIVER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(DRIVER)
EXPECTED = {
    "highChannel_stripped", "highChannel_restrict", "restricted_stripped_zero",
    "shear", "shear_incoming", "shear_outgoing", "shear_overlap",
    "projection_shear_failure", "shear_filtered", "shear_stripped",
    "finite_sector_discrepancy", "shearProfile_initial", "rgTime_exp_neg",
    "shearProfile_derivative", "scaled_shearProfile", "active_stripped_tail",
    "tail_div_gSquared", "tailRatio_limit", "tail_not_flat",
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ym-lean", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path,
                        help="New output directory; existing evidence is not overwritten")
    args = parser.parse_args()
    root, out = args.ym_lean.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = HERE / "FilteredSectorProbe.lean"
    env = dict(os.environ, LEAN_NUM_THREADS="3")
    command = ["lake", "env", "lean", "-DwarningAsError=true", str(source)]
    report = {
        "status": "DIAGNOSTIC_FAILED",
        "scope": "Finite filtered-sector projection/transport diagnostic only",
        "existence_only_kernel_certificate": False,
        "full_generated_countermodel_constructed": False,
        "verifier_revision": DRIVER.PIN["revision"],
        "source_sha256": DRIVER.digest(source),
        "runner_sha256": DRIVER.digest(Path(__file__).resolve()),
        "command": command,
    }
    code = 1
    try:
        DRIVER.check_pin(root, env)
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                capture_output=True, timeout=180)
        log = result.stdout + result.stderr
        (out / "lean.log").write_text(log, encoding="utf-8")
        DRIVER.check_pin(root, env)
        report["lean_exit_code"] = result.returncode
        matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
        axioms = {name: sorted(a.strip() for a in raw.split(",") if a.strip())
                  for name, raw in matches}
        expected = {"YMYMGAudit." + name for name in EXPECTED}
        if result.returncode != 0:
            raise RuntimeError("Lean compilation failed")
        if len(matches) != len(expected) or set(axioms) != expected:
            raise RuntimeError("Missing, duplicate, or unexpected declaration audit")
        if any(set(used) - DRIVER.ALLOWED for used in axioms.values()):
            raise RuntimeError("Unapproved axiom dependency")
        report.update(status="FINITE_SECTOR_DIAGNOSTIC_CHECKED", axioms=axioms,
                      trusted_checkout_unchanged=True)
        code = 0
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (out / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: report[k] for k in (
        "status", "scope", "existence_only_kernel_certificate",
        "full_generated_countermodel_constructed")}, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
