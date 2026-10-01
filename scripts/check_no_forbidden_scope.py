#!/usr/bin/env python3
"""Lean source policy for S2a: forbidden constructs, forbidden scope, required theorem inventory.

Scans code only (comments and string literals stripped), so prose may discuss these topics.
`--list-theorems` prints the fully qualified name of every non-private `theorem` of the checker
library, in source order (used to generate and verify `P10S2/AxiomAudit.lean`).
Exit 0 = clean.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent


def strip(src: str) -> str:
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        two = src[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1; i += 2
            elif two == "-/":
                depth -= 1; i += 2
            else:
                i += 1
        elif two == "/-":
            depth = 1; i += 2
        elif two == "--":
            while i < n and src[i] != "\n":
                i += 1
        elif src[i] == '"':
            i += 1
            while i < n and src[i] != '"':
                i += 2 if src[i] == "\\" else 1
            i += 1
            out.append('""')
        else:
            out.append(src[i]); i += 1
    return "".join(out)


FORBIDDEN_CONSTRUCTS = [
    r"\bsorry\b", r"\badmit\b", r"\baxiom\b", r"\bnative_decide\b",
    r"\bunsafe\b", r"\bmeta\b", r"\bimplemented_by\b", r"\bextern\b",
    r"\brun_cmd\b", r"\binitialize\b", r"\bopaque\b", r"\bpartial\b",
    r"\belab\b", r"\bmacro\b", r"\bsyntax\b", r"\bnotation\b", r"\bunif_hint\b",
    r"\bimport\s+Lean\b", r"\bopen\s+Lean\b", r"\baddDecl\b",
    r"\bLean\.ofReduceBool\b", r"\bsorryAx\b", r"\bset_option\s+(?!maxRecDepth)\w+",
]
# S2a must not contain production crypto/network/SCITT code (those are S2b / S3).
FORBIDDEN_SCOPE = [
    r"(?i)\bcose\b", r"(?i)\bcwt\b", r"(?i)ed25519", r"(?i)ecdsa", r"(?i)verifySig",
    r"(?i)scrapi", r"(?i)\bhttps?\b", r"(?i)socket", r"(?i)\bdid:", r"(?i)x509",
    r"(?i)\bscitt\b", r"(?i)IO\.Process", r"(?i)\bTcp\b",
]
CHECKER_SRC = [ROOT / "P10S2.lean"] + sorted((ROOT / "P10S2").glob("*.lean"))
ALL_SRC = CHECKER_SRC + [ROOT / "P10S2Tests.lean"] + sorted((ROOT / "P10S2Tests").glob("*.lean")) \
    + sorted((ROOT / "P10S2TestsMustFail").glob("*.lean"))

# The theorem inventory demanded by prereg §15 (names in `namespace P10S2`).
REQUIRED = [
    "P10S2.decode_encode_transcript", "P10S2.encode_decode_transcript",
    "P10S2.decode_encode_profile", "P10S2.encode_decode_profile",
    "P10S2.fx_projection", "P10S2.bundle_perm", "P10S2.bundle_dedup",
    "P10S2.bundle_faithful", "P10S2.bundle_refines",
    "P10S2.coverage_sound", "P10S2.coverage_sound_view", "P10S2.s2_end_to_end",
    "P10S2.p10Verdict_halt", "P10S2.p10Verdict_reject", "P10S2.coverage_halt_no_verdict",
]


def qualified_theorems():
    names = []
    for f in CHECKER_SRC:
        ns = []
        for line in strip(f.read_text()).splitlines():
            m = re.match(r"\s*namespace\s+([\w.]+)", line)
            if m:
                ns.append(m.group(1)); continue
            m = re.match(r"\s*end\s+([\w.]+)", line)
            if m and ns and ns[-1] == m.group(1):
                ns.pop(); continue
            m = re.match(r"\s*(?:@\[[^\]]*\]\s*)?theorem\s+([\w.']+)", line)
            if m:
                names.append(".".join(ns + [m.group(1)]))
    return names


def main() -> int:
    if "--list-theorems" in sys.argv:
        print("\n".join(qualified_theorems()))
        return 0
    fail = []
    for f in ALL_SRC:
        code = strip(f.read_text())
        rel = f.relative_to(ROOT)
        for pat in FORBIDDEN_CONSTRUCTS:
            if re.search(pat, code):
                fail.append(f"{rel}: forbidden construct /{pat}/")
        if f in CHECKER_SRC or "P10S2Tests" in str(rel):
            for pat in FORBIDDEN_SCOPE:
                if re.search(pat, code):
                    fail.append(f"{rel}: out-of-scope (S2b/S3) /{pat}/")
        for line in code.splitlines():
            m = re.match(r"\s*import\s+(\S+)", line)
            if m and not (m.group(1).startswith("P10S2") or m.group(1).startswith("P10.")):
                fail.append(f"{rel}: external import {m.group(1)}")
    # partition rule, source level: the checker library never imports the test library
    for f in CHECKER_SRC:
        for line in strip(f.read_text()).splitlines():
            m = re.match(r"\s*import\s+(\S+)", line)
            if m and m.group(1).startswith("P10S2Tests"):
                fail.append(f"{f.relative_to(ROOT)}: checker imports test library {m.group(1)}")
    have = set(qualified_theorems())
    for r in REQUIRED:
        if r not in have:
            fail.append(f"required theorem missing: {r}")
    lake = (ROOT / "lakefile.toml").read_text()
    reqs = re.findall(r'(?ms)^\[\[require\]\]\s*name\s*=\s*"([^"]+)"\s*path\s*=\s*"([^"]+)"', lake)
    if reqs != [("p10-underdetermination-lean-s1", "vendor/p10-underdetermination-lean-s1")]:
        fail.append(f"lakefile.toml: unexpected dependencies {reqs}")
    if "git" in re.sub(r"#.*", "", lake):
        fail.append("lakefile.toml: git dependency not allowed")
    if fail:
        print("\n".join(fail))
        return 1
    print("lean source policy: clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
