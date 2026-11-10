#!/usr/bin/env python3
"""Reproduce the October submission and review checks; Python standard library only.

SPDX-License-Identifier: Apache-2.0
Every invocation creates a new evidence directory. See docs/rerun.md for scope.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import importlib.util
import json
import os
import platform
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}


def now():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def capture(command, cwd, env=None):
    return subprocess.check_output(command, cwd=cwd, env=env, text=True).strip()


def integrity(source):
    expected = json.loads((ROOT / "provenance/october-import.json").read_text())
    for item in expected["included"]:
        rel = Path(item["path"]).relative_to("submission")
        require(sha(source / rel) == item["sha256"], "Changed submitted file: " + str(rel))
    modules = json.loads((ROOT / "provenance/review-imports.json").read_text())["files"]
    for item in modules:
        require(sha(ROOT / item["path"]) == item["sha256"], "Changed review source: " + item["path"])
    manifest = ROOT / "provenance/package-files.json"
    for rel, digest in json.loads(manifest.read_text()).items():
        require(sha(ROOT / rel) == digest, "Changed packaged input: " + rel)
    return dict(submission_files=len(expected["included"]), review_modules=len(modules),
                submission_manifest_sha256=sha(source / "SOURCES.sha256"), passed=True)


def os_correspondence():
    spec = importlib.util.spec_from_file_location("normalization", ROOT / "provenance/normalization-source.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    checks = [
        ("OSInnerProduct", "Specification.lean", "YangMills/OSRecon/Vendored/Axioms.lean"),
        ("OsterwalderSchraderAxioms", "Specification.lean", "YangMills/OSRecon/Vendored/Axioms.lean"),
        ("OSArityLinearGrowthCondition", "Specification.lean", "YangMills/OSRecon/Growth.lean"),
        ("BorchersSequence", "Specification/Wightman.lean", "YangMills/OSRecon/Vendored/OSConj.lean"),
    ]
    results = []
    for name, original, local in checks:
        a = mod.declaration((ROOT / "provenance/osreconstruction" / original).read_text(), name)
        b = mod.declaration((ROOT / "checks" / local).read_text(), name)
        require(a and b and mod.normalize(a) == mod.normalize(b), "OS declaration mismatch: " + name)
        results.append(dict(name=name, upstream=original, local=local, whole_declaration_matches=True))
    return dict(passed=True, declarations=results,
                limitation="Text correspondence after documented normalization; full upstream projects are not jointly compiled.")


def dependency_pins(source, env, lake):
    records = []
    for p in json.loads((source / "lake-manifest.json").read_text())["packages"]:
        directory = source / ".lake/packages" / p["name"]
        actual = capture(["git", "rev-parse", "HEAD"], directory, env)
        dirty = capture(["git", "status", "--porcelain", "--untracked-files=no"], directory, env)
        require(actual == p["rev"] and not dirty, "Dependency differs from pin: " + p["name"])
        records.append(dict(name=p["name"], revision=actual, tracked_changes=False))
    version = capture([lake, "env", "lean", "--version"], source, env)
    require("version 4.32.0," in version, "Wrong submission Lean version: " + version)
    return dict(lean=version, packages=records)


def prepare(project, source):
    shutil.copytree(ROOT / "checks", project)
    for name in ["AcceptanceChallenge", "OPEChallenge"]:
        shutil.copy2(ROOT / "verification" / (name + ".lean"), project / (name + ".lean"))
    roots = sorted(str(p.relative_to(project).with_suffix("")).replace(os.sep, ".")
                   for p in project.rglob("*.lean"))
    shutil.copy2(source / "lean-toolchain", project / "lean-toolchain")
    (project / "lakefile.toml").write_text(
        'name = "pureym_review"\nversion = "0.1.0"\npackagesDir = ' +
        json.dumps(str(source / ".lake/packages")) + '\n[leanOptions]\nmaxHeartbeats = 0\nmaxRecDepth = 4096\n'
        '[[lean_lib]]\nname = "Review"\nroots = ' + json.dumps(roots) + '\n'
        '[[require]]\nname = "ym_core"\npath = ' + json.dumps(str(source)) + '\n')
    manifest = json.loads((source / "lake-manifest.json").read_text())
    manifest.update(name="pureym_review", packagesDir=str(source / ".lake/packages"))
    for p in manifest["packages"]:
        p["inherited"] = True
    manifest["packages"].append(dict(type="path", name="ym_core", scope="", dir=str(source),
        inherited=False, configFile="lakefile.toml", manifestFile="lake-manifest.json"))
    write(project / "lake-manifest.json", manifest)
    for name in ["acceptance", "ope"]:
        shutil.copy2(ROOT / "verification" / (name + ".json"), project / (name + ".json"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", choices=["integrity", "build", "review", "tools", "prepare", "controls", "comparator", "all"])
    parser.add_argument("--run-dir", type=Path, help="New output directory; must not already exist")
    parser.add_argument("--source", type=Path, default=ROOT / "submission", help="Exact original source, optionally already built")
    parser.add_argument("--tools-dir", type=Path, default=ROOT / ".tools")
    parser.add_argument("--target", choices=["all", "submission", "acceptance", "ope"], default="all")
    parser.add_argument("--lake", default=shutil.which("lake") or str(Path.home() / ".elan/bin/lake"))
    args = parser.parse_args()
    source = args.source.resolve()
    toolroot = args.tools_dir.resolve()
    out = (args.run_dir or ROOT / "runs" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    for key in ["LEAN_PATH", "LEAN_SRC_PATH", "COMPARATOR_LANDRUN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_NANODA"]:
        env.pop(key, None)
    env["PATH"] = str(Path(args.lake).absolute().parent) + os.pathsep + env.get("PATH", "")
    record = dict(started_utc=now(), stage=args.stage, status="running", source=str(source),
                  platform=platform.platform(), run_directory=str(out), commands=[],
                  source_build_present_at_start=(source / ".lake/build").exists(),
                  LEAN_NUM_THREADS=env.get("LEAN_NUM_THREADS"),
                  comparator_mode="upstream development launcher; no Landrun isolation or external kernel")

    def save():
        write(out / "result.json", record)

    def run(name, command, cwd, overrides=None, expected_code=0, diagnostic=None):
        rec = dict(name=name, command=[str(c) for c in command], cwd=str(cwd), started_utc=now())
        record["commands"].append(rec)
        save()
        start = time.monotonic()
        print(name + ": started", flush=True)
        with (out / (name + ".log")).open("w") as log:
            code = subprocess.call(command, cwd=cwd, env=dict(env, **(overrides or {})), stdout=log, stderr=subprocess.STDOUT)
        output = (out / (name + ".log")).read_text()
        correct = (code == expected_code if expected_code is not None else code != 0)
        correct = correct and (diagnostic is None or diagnostic in output)
        rec.update(exit_code=code, finished_utc=now(), seconds=round(time.monotonic()-start, 3),
                   expected_behavior=correct, log=name + ".log")
        save()
        require(correct, name + " failed; see " + str(out / (name + ".log")))
        print(name + ": passed", flush=True)
        return output

    try:
        record["integrity_before"] = integrity(source)
        record["os_correspondence"] = os_correspondence()
        save()
        if args.stage in {"build", "all"}:
            run("dependency-cache", [args.lake, "exe", "cache", "get"], source)
            record["dependencies"] = dependency_pins(source, env, args.lake)
            log = run("submission-build", [args.lake, "build", "WilsonReference", "WilsonConstruction"], source)
            record["submission_warning_lines"] = [s for s in log.splitlines() if "warning:" in s]
        if args.stage in {"review", "all"}:
            record["dependencies"] = dependency_pins(source, env, args.lake)
            build = out / "review-objects"
            build.mkdir()
            base = capture([args.lake, "env", "printenv", "LEAN_PATH"], source, env)
            lean = capture([args.lake, "env", "which", "lean"], source, env)
            local = {str(p.relative_to(ROOT / "checks").with_suffix("")).replace(os.sep, "."): p
                     for p in (ROOT / "checks").rglob("*.lean")}
            ordered, visiting = [], set()

            def visit(name):
                if name in ordered or name not in local:
                    return
                require(name not in visiting, "Cyclic review import: " + name)
                visiting.add(name)
                for dep in re.findall(r"^import\s+([A-Za-z0-9_.]+)", local[name].read_text(), re.M):
                    visit(dep)
                visiting.remove(name)
                ordered.append(name)

            visit("AxiomAudit")
            visit("OPECheck")
            require(set(ordered) == set(local), "Review bundle contains unbuilt modules")
            reports = []
            for name in ordered:
                target = build / (name.replace(".", "/") + ".olean")
                target.parent.mkdir(parents=True, exist_ok=True)
                log = run("review-" + name, [lean, "--root=" + str(ROOT / "checks"), "-o", str(target), str(local[name])],
                          source, {"LEAN_PATH": str(build) + os.pathsep + base})
                require(not re.search(r"\b(?:error|warning):", log), "Review warning/error in " + name)
                reports += re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
            expected = {"YMReview.Acceptance." + n for n in ["finite_law_on_family", "lattice_and_scale", "phase_and_os",
                "translation_ward", "operator_content", "leading_trace", "accepted_of_source", "combined_acceptance"]}
            expected |= {"YMReview.OPE." + n for n in ["from_source", "phase_difference", "constructed", "channel_assembly", "single_field"]}
            require({n for n, _ in reports} == expected and len(reports) == len(expected), "Axiom audit did not cover exactly the 13 expected declarations")
            for name, axioms in reports:
                require(set(re.findall(r"[\w.]+", axioms)) <= PERMITTED, "Unexpected axioms: " + name + " " + axioms)
            record["review"] = dict(modules=len(ordered), warnings=0, fresh_review_objects=True,
                declarations=[dict(name=n, axioms=re.findall(r"[\w.]+", a)) for n, a in reports])
        if args.stage in {"tools", "all"}:
            toolroot.mkdir(parents=True, exist_ok=True)
            for pin in json.loads((ROOT / "verification/tool-pins.json").read_text())["tools"]:
                checkout = toolroot / pin["name"]
                if not checkout.exists():
                    run("clone-" + pin["name"], ["git", "clone", "--no-checkout", pin["url"], str(checkout)], ROOT)
                    run("checkout-" + pin["name"], ["git", "checkout", "--detach", pin["revision"]], checkout)
                require(capture(["git", "rev-parse", "HEAD"], checkout, env) == pin["revision"], "Wrong tool revision: " + pin["name"])
                require(not capture(["git", "status", "--porcelain", "--untracked-files=no"], checkout, env), "Modified tool sources: " + pin["name"])
                run("build-" + pin["name"], [args.lake, "build", pin["name"]], checkout)
        if args.stage in {"prepare", "comparator", "all"}:
            project = out / "project"
            prepare(project, source)
            record["prepared_project"] = str(project)
        if args.stage in {"controls", "comparator", "all"}:
            tool_records = []
            for pin in json.loads((ROOT / "verification/tool-pins.json").read_text())["tools"]:
                directory = toolroot / pin["name"]
                require(capture(["git", "rev-parse", "HEAD"], directory, env) == pin["revision"], "Tool revision mismatch")
                require(not capture(["git", "status", "--porcelain", "--untracked-files=no"], directory, env), "Tool sources modified")
                binary = directory / ".lake/build/bin" / pin["name"]
                require(binary.is_file(), "Build pinned tools first: " + str(binary))
                tool_records.append(dict(**pin, binary_sha256=sha(binary)))
            record["tools"] = tool_records
            comparator = toolroot / "comparator/.lake/build/bin/comparator"
            launcher = toolroot / "comparator/scripts/fake-landrun.sh"
            overrides = dict(COMPARATOR_LANDRUN=str(launcher),
                             COMPARATOR_LEAN4EXPORT=str(toolroot / "lean4export/.lake/build/bin/lean4export"))
            record["launcher_sha256"] = sha(launcher)
            record["environment_overrides"] = overrides
            controls = out / "controls"
            shutil.copytree(ROOT / "verification/controls", controls)
            reasons = {
                "accept": "Your solution is okay!",
                "statement_mismatch": "Challenge and solution theorem statement do not match: 'comparatorSmoke'",
                "forbidden_axiom": "Illegal axiom detected: 'unapproved'",
                "definition_mismatch": "Const does not match between challenge and target 'reference'",
            }
            for case, reason in reasons.items():
                run("control-" + case, [args.lake, "env", str(comparator), "comparator.json"], controls / case,
                    overrides, 0 if case == "accept" else None, reason)
            record["controls_passed"] = True
            if args.stage != "controls":
                record["dependencies"] = dependency_pins(source, env, args.lake)
                targets = ["submission", "acceptance", "ope"] if args.target == "all" else [args.target]
                for target in targets:
                    cwd = source if target == "submission" else project
                    config = ROOT / "verification/submission.json" if target == "submission" else project / (target + ".json")
                    log = run("comparator-" + target, [args.lake, "env", str(comparator), str(config)], cwd,
                              overrides, 0, "Your solution is okay!")
                    require("Lean default kernel accepts the solution" in log, "Missing kernel acceptance message")
        record["integrity_after"] = integrity(source)
        record.update(status="passed", finished_utc=now())
        save()
        print("Results: " + str(out / "result.json"), flush=True)
    except BaseException as exc:
        record.update(status="failed", error=repr(exc), finished_utc=now())
        save()
        raise


if __name__ == "__main__":
    main()
