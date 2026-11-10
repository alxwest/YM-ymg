#!/usr/bin/env python3
"""Check the vendored OSreconstruction declarations against the published package.

The corrected OS and Wightman records were published on 2026-09-10 as a
self-contained source distribution, `os-reconstruction/`, on the branch
`codex/publish-os-proof-package-20260910` of xiyin137/OSreconstruction
(commit 32b6102).  That package is on Lean v4.29 while this repository is on
v4.33-rc1, so it cannot be a Lake dependency and the statement surface is
vendored in `YangMills/OSRecon/Vendored/`.  This script checks that what is
vendored is what was published.

Usage (from the repository root):

    python3 scripts/check_vendored_osrecon.py [path-to-OSreconstruction-checkout]

The checkout must contain the published branch; the script reads the files out
of Git at the pinned commit, so the working tree may be on any branch.
Output is written to stdout and saved in scripts/check_vendored_osrecon.out.

Two declarations differ from the published text in ways that do not change the
proposition, and the script rewrites for them explicitly rather than hiding it:

* `osArityLinearSchwartzSeminorm d n s` is the published abbreviation for the
  seminorm this repository writes out, `(Finset.Iic (n*s, n*s)).sup
  (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ)`;
* the published sources spell the base types `Nat`, `Real`, `Complex` in the
  files written after the correction and `ℕ`, `ℝ`, `ℂ` elsewhere;
* the published `OSLinearGrowthCondition` is an abbreviation for the
  arity-linear condition, which this repository calls
  `OSArityLinearGrowthCondition` because the shorter name is taken by the
  superseded fixed-order condition (upstream `OSFixedOrderGrowthCondition`).

Differences in *proof* text are expected and reported as `[proof ported]`: the
proofs were ported to this repository's toolchain, the statements were not.
"""
import re
import subprocess
import sys
import pathlib

COMMIT = "32b6102"
PKG = "os-reconstruction/OSReconstruction"
ROOT = pathlib.Path(__file__).resolve().parent.parent

# (declaration, published file, vendored file)
CHECKS = [
    ("OSInnerProduct", "Specification.lean", "YangMills/OSRecon/Vendored/Axioms.lean"),
    ("OsterwalderSchraderAxioms", "Specification.lean", "YangMills/OSRecon/Vendored/Axioms.lean"),
    ("OSArityLinearGrowthCondition", "Specification.lean", "YangMills/OSRecon/Growth.lean"),
    ("wickRotatePoint", "Wightman/WightmanAxioms.lean", "YangMills/OSRecon/Vendored/Reconstruction.lean"),
    ("IsWickRotationPair", "Specification.lean", "YangMills/OSRecon/Vendored/Reconstruction.lean"),
    ("EToRStatement", "Specification.lean", "YangMills/OSRecon/Vendored/Reconstruction.lean"),
    ("RToEStatement", "Specification.lean", "YangMills/OSRecon/Vendored/Reconstruction.lean"),
    ("BorchersSequence", "Specification/Wightman.lean", "YangMills/OSRecon/Vendored/OSConj.lean"),
    ("IsNormalized", "Specification/Wightman.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("IsTranslationInvariantWeak", "Specification/Wightman.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("IsLorentzCovariantWeak", "Specification/Wightman.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("IsAdjacentLocallyCommutativeWeak", "Specification/Wightman.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("WightmanInnerProduct", "Specification/Wightman.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("Wightman.IsPositiveDefinite", "Specification/Wightman.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("WightmanFunctions", "Specification/Wightman.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("ForwardMomentumCone", "Wightman/WightmanAxioms.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("InOpenForwardCone", "Wightman/WightmanAxioms.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("InForwardCone", "Wightman/WightmanAxioms.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("ForwardTube", "Wightman/WightmanAxioms.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("ForwardConeAbs", "Wightman/SpectralCondition.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("ForwardTubeAnalyticityCompactSubset", "Wightman/SpectralCondition.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("SpectralConditionDistribution", "Wightman/SpectralCondition.lean", "YangMills/OSRecon/Vendored/Wightman.lean"),
    ("SchwartzNPointSpace.fourierTransform", "Wightman/SpectralCondition.lean", "YangMills/OSRecon/Vendored/DiffVarReduction.lean"),
    ("nPointToEuclidean", "Wightman/SpectralCondition.lean", "YangMills/OSRecon/Vendored/DiffVarReduction.lean"),
    ("uncurryLinearEquivSpec", "Wightman/SpectralCondition.lean", "YangMills/OSRecon/Vendored/DiffVarReduction.lean"),
    ("diffVarSection", "Wightman/SpectralCondition.lean", "YangMills/OSRecon/Vendored/DiffVarReduction.lean"),
    ("diffVarReduction", "Wightman/SpectralCondition.lean", "YangMills/OSRecon/Vendored/DiffVarReduction.lean"),
]

DECL_HEAD = (r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |public )*"
             r"(?:structure|def|abbrev|theorem|lemma) ")


def declaration(text, name):
    """The source of the named declaration: its head line and indented body."""
    lines = text.splitlines()
    head = re.compile(DECL_HEAD + re.escape(name) + r"(?![A-Za-z0-9_'])")
    for i, line in enumerate(lines):
        if head.match(line):
            break
    else:
        return None
    out, j = [lines[i]], i + 1
    while j < len(lines):
        line = lines[j]
        if line and not line[0].isspace() and not line.startswith((")", "}")):
            if re.match(DECL_HEAD + r"|^(?:/-|end|namespace|open|variable|section|"
                        r"set_option|import|@\[)", line):
                break
        out.append(line)
        j += 1
    return "\n".join(out)


def statement(text):
    """The proposition: the declaration with its proofs and values removed.

    For a structure this is its field list; a field's default value is a proof
    of that field, not part of what the field asserts, so it is cut like any
    other proof.  The structures checked here have at most one default, on
    their last field.
    """
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = re.sub(r"--.*", "", text)
    return re.split(r":=|\bwhere\b", text)[0]


def normalize(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = re.sub(r"--.*", "", text)
    text = re.sub(r"\bNat\b", "ℕ", text)
    text = re.sub(r"\bReal\b", "ℝ", text)
    text = re.sub(r"\bComplex\b(?!\.)", "ℂ", text)
    # the published abbreviation for the seminorm written out here
    text = re.sub(r"osArityLinearSchwartzSeminorm\s+d\s+n\s+sobolev_index",
                  "(Finset.Iic (n * sobolev_index, n * sobolev_index)).sup "
                  "(schwartzSeminormFamily ℝ (NPointDomain d n) ℂ)", text)
    # the published `OSLinearGrowthCondition` is an abbreviation for this
    text = re.sub(r"\bOSLinearGrowthCondition\b", "OSArityLinearGrowthCondition", text)
    # `d` is a section variable here and an explicit binder there
    text = re.sub(r"\(d\s*:\s*ℕ\)\s*\[NeZero d\]\s*", "", text)
    text = re.sub(r"\s+", " ", text)
    return text.strip()


def main():
    checkout = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else \
        ROOT.parent / "OSreconstruction"
    if not (checkout / ".git").exists():
        sys.exit(f"not a Git checkout: {checkout}")
    print(f"published package: {checkout} at {COMMIT}, {PKG}/")
    print(f"vendored in:       {ROOT}/YangMills/OSRecon/\n")
    published = {}
    for _, path, _ in CHECKS:
        if path in published:
            continue
        try:
            published[path] = subprocess.check_output(
                ["git", "show", f"{COMMIT}:{PKG}/{path}"], cwd=checkout,
                stderr=subprocess.DEVNULL).decode()
        except subprocess.CalledProcessError:
            sys.exit(f"cannot read {PKG}/{path} at {COMMIT} in {checkout}; "
                     f"fetch the branch codex/publish-os-proof-package-20260910")
    ok = differs = missing = 0
    for name, path, mine in CHECKS:
        theirs = declaration(published[path], name)
        ours = declaration((ROOT / mine).read_text(), name)
        if theirs is None or ours is None:
            where = "published" if theirs is None else "vendored"
            print(f"  MISSING  {name}  (not found in the {where} source)")
            missing += 1
            continue
        if normalize(statement(theirs)) == normalize(statement(ours)):
            tail = "" if normalize(theirs) == normalize(ours) else "   [proof ported]"
            print(f"  same     {name}{tail}")
            ok += 1
        else:
            print(f"  DIFFERS  {name}   in {mine}")
            differs += 1
    print(f"\n{ok} statements identical, {differs} differing, {missing} missing, "
          f"of {len(CHECKS)} checked.")
    return 1 if (differs or missing) else 0


if __name__ == "__main__":
    sys.exit(main())
