#!/usr/bin/env python3
"""Scaffold gate: forbidden Lean constructs, forbidden scope, premature claims.

Scans code only (comments and string literals stripped), so prose in docs and
doc-comments may discuss these topics.
"""
import pathlib, re, sys

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
    r"\belab\b", r"\bmacro\b", r"\bsyntax\b", r"\bset_option\s+maxRecDepth\b",
]
FORBIDDEN_SCOPE = [
    r"(?i)cose", r"(?i)\bcwt\b", r"(?i)ed25519", r"(?i)ecdsa", r"(?i)sha-?256", r"(?i)verifySig", r"(?i)scrapi", r"(?i)http",
    r"(?i)socket", r"(?i)\bdid:", r"(?i)x509", r"(?i)merkle", r"(?i)\bvds\b",
    r"(?i)scitt", r"(?i)receipt", r"(?i)IO\.Process", r"(?i)System\.FilePath",
]
# Premature-claim gate: these must not be DECLARED at scaffold stage.
PREMATURE = r"\b(?:def|theorem|lemma|abbrev|structure|inductive)\s+(?:\w+\.)*(coverageCheck|coverage_sound|coverage_then_underdetermined|CoverageSpec|bundle_perm)\b"

THEOREM_DECL = r"(?m)^\s*(?:theorem|lemma)\s+([A-Za-z0-9_.']+)"

if "--list-theorems" in sys.argv:
    for f in sorted((ROOT / "P10S2").glob("*.lean")):
        for name in re.findall(THEOREM_DECL, strip(f.read_text())):
            print(name)
    sys.exit(0)

fail = []
files = sorted((ROOT / "P10S2").glob("*.lean")) + [ROOT / "P10S2.lean"]
for f in files:
    code = strip(f.read_text())
    for pat in FORBIDDEN_CONSTRUCTS:
        if re.search(pat, code):
            fail.append(f"{f.relative_to(ROOT)}: forbidden construct /{pat}/")
    for pat in FORBIDDEN_SCOPE:
        if re.search(pat, code):
            fail.append(f"{f.relative_to(ROOT)}: out-of-scope (S2b/S3) /{pat}/")
    m = re.search(PREMATURE, code)
    if m:
        fail.append(f"{f.relative_to(ROOT)}: premature declaration `{m.group(1)}`")

lake = (ROOT / "lakefile.toml").read_text()
if re.search(r"(?m)^\s*require\b", lake):
    fail.append("lakefile.toml: unexpected `require` dependency")
if '"packages": []' not in (ROOT / "lake-manifest.json").read_text():
    fail.append("lake-manifest.json: unexpected packages")
for f in list((ROOT / "P10S2").glob("*.lean")):
    for line in f.read_text().splitlines():
        m = re.match(r"\s*import\s+(\S+)", line)
        if m and not m.group(1).startswith("P10S2."):
            fail.append(f"{f.relative_to(ROOT)}: external import {m.group(1)}")

if fail:
    print("\n".join(fail)); sys.exit(1)
print("forbidden-construct/scope check: clean")
