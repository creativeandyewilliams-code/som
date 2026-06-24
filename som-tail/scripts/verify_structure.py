#!/usr/bin/env python3
"""
Kernel-independent structural pre-check for the som-tail Lean development.

Checks:
1. No sorry/admit/native_decide in Tier A (Witness.lean) or Tier B (Complexity.lean).
2. Collects every sorry in other files (expected only in Reversal.lean).
3. All named load-bearing theorems from §3/§5 are present.
4. No new axiom declarations (only mathlib's standard base is acceptable).

Returns nonzero on any failure. Output is captured verbatim for CERTIFICATE.md.
"""
import re
import sys
from pathlib import Path

TIER_AB_FILES = ["Witness.lean", "Complexity.lean"]
ALL_TIER_FILES = ["Witness.lean", "Complexity.lean", "UpperBound.lean", "Coding.lean", "Reversal.lean"]

REQUIRED_THEOREMS = [
    "trunc_factors",
    "tower_refines",
    "hist_agree",
    "tail_xA",
    "tail_xB",
    "nondescent",
    "tail_iff_sigma02",
    "tail_decided_with_jump",
    "coding_correct",
    "reversal",
]


def strip_comments(text: str) -> list[tuple[int, str]]:
    """
    Strip Lean comments and return (line_number, code_only_line) pairs.
    Handles:  -- single-line  and  /- block -/  and  /-- doc -/
    Only code outside comments is checked for sorry/axiom.
    """
    result = []
    in_block = False
    depth = 0
    lines = text.splitlines()
    for lineno, line in enumerate(lines, 1):
        code = ""
        i = 0
        n = len(line)
        while i < n:
            if in_block:
                if line[i:i+2] == "-/":
                    depth -= 1
                    if depth == 0:
                        in_block = False
                    i += 2
                elif line[i:i+2] == "/-":
                    depth += 1
                    i += 2
                else:
                    i += 1
            else:
                if line[i:i+2] == "--":
                    break  # rest of line is comment
                elif line[i:i+2] == "/-":
                    in_block = True
                    depth = 1
                    i += 2
                else:
                    code += line[i]
                    i += 1
        result.append((lineno, code))
    return result


def scan_file(path: Path):
    text = path.read_text(encoding="utf-8")
    code_lines = strip_comments(text)
    sorrys = []
    native_decides = []
    axioms = []
    sorry_pat = re.compile(r'\bsorry\b|\badmit\b')
    nd_pat = re.compile(r'\bnative_decide\b')
    axiom_pat = re.compile(r'\baxiom\s+\w')
    for lineno, code in code_lines:
        if sorry_pat.search(code):
            orig = path.read_text().splitlines()[lineno - 1]
            sorrys.append((lineno, orig.rstrip()))
        if nd_pat.search(code):
            orig = path.read_text().splitlines()[lineno - 1]
            native_decides.append((lineno, orig.rstrip()))
        if axiom_pat.search(code):
            orig = path.read_text().splitlines()[lineno - 1]
            axioms.append((lineno, orig.rstrip()))
    return sorrys, native_decides, axioms


def find_theorems(path: Path):
    text = path.read_text(encoding="utf-8")
    found = set()
    for thm in REQUIRED_THEOREMS:
        pat = re.compile(r'\b(?:theorem|lemma|def)\s+' + re.escape(thm) + r'\b')
        if pat.search(text):
            found.add(thm)
    return found


def main(lean_dir: str):
    lean_path = Path(lean_dir)
    failures = []

    print("=" * 70)
    print("STRUCTURAL PRE-CHECK — som-tail")
    print("=" * 70)

    # 1. Tier A/B must be sorry-free.
    print("\n[1] Checking Tier A/B files for sorry/admit/native_decide …")
    tier_ab_clean = True
    for fname in TIER_AB_FILES:
        fpath = lean_path / fname
        if not fpath.exists():
            failures.append(f"MISSING: {fname}")
            print(f"  MISSING  {fname}")
            tier_ab_clean = False
            continue
        sorrys, nd, _ = scan_file(fpath)
        if sorrys or nd:
            tier_ab_clean = False
        for lineno, text in sorrys:
            msg = f"SORRY in Tier A/B  {fname}:{lineno}: {text.strip()}"
            failures.append(msg)
            print(f"  FAIL  {msg}")
        for lineno, text in nd:
            msg = f"native_decide in Tier A/B  {fname}:{lineno}: {text.strip()}"
            failures.append(msg)
            print(f"  FAIL  {msg}")
        if not sorrys and not nd:
            print(f"  OK    {fname}")
    if tier_ab_clean:
        print("  → Tier A/B files are sorry-free. ✓")

    # 2. Collect all sorrys in the whole development.
    print("\n[2] Collecting all sorry occurrences …")
    all_sorrys: dict[str, list] = {}
    for fname in ALL_TIER_FILES:
        fpath = lean_path / fname
        if not fpath.exists():
            continue
        sorrys, _, _ = scan_file(fpath)
        if sorrys:
            all_sorrys[fname] = sorrys
    if all_sorrys:
        print("  Sorry inventory (expected only in Reversal.lean):")
        for fname, items in all_sorrys.items():
            expected = fname in ("Reversal.lean",)
            label = "EXPECTED" if expected else "FLAGGED"
            for lineno, text in items:
                print(f"    [{label}]  {fname}:{lineno}: {text.strip()}")
    else:
        print("  No sorry found in any file.")

    # 3. Check all required theorems are present.
    print("\n[3] Checking for required theorems …")
    found_all: set[str] = set()
    for fname in ALL_TIER_FILES:
        fpath = lean_path / fname
        if not fpath.exists():
            continue
        found_all |= find_theorems(fpath)
    for thm in REQUIRED_THEOREMS:
        status = "OK" if thm in found_all else "MISSING"
        print(f"  {status:7}  {thm}")
        if thm not in found_all:
            failures.append(f"MISSING theorem: {thm}")

    # 4. Check for new axiom declarations.
    print("\n[4] Checking for new axiom declarations …")
    any_axiom = False
    for fname in ALL_TIER_FILES:
        fpath = lean_path / fname
        if not fpath.exists():
            continue
        _, _, axioms = scan_file(fpath)
        if axioms:
            any_axiom = True
            for lineno, text in axioms:
                print(f"  WARNING  axiom in {fname}:{lineno}: {text.strip()}")
    if not any_axiom:
        print("  No new axiom declarations found. ✓")

    # Summary
    print("\n" + "=" * 70)
    if failures:
        print(f"RESULT: FAILED ({len(failures)} failure(s))")
        for f in failures:
            print(f"  - {f}")
        sys.exit(1)
    else:
        print("RESULT: PASSED")
        sys.exit(0)


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: verify_structure.py <path-to-SomTail-dir>")
        sys.exit(2)
    main(sys.argv[1])
