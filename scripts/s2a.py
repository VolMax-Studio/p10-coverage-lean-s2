#!/usr/bin/env python3
"""S2a acceptance harness (prereg §6a, §15). Part of the verifier manifest.

Subcommands
  gen-verifier / check-verifier   write / recompute-and-compare VerifierManifestS2aV0
  gen-vector   / check-vector     write / recompute-and-compare VectorManifestS2aV0 (+ file-set equality)
  partition                       manifest partition rule (source, .olean imports, digest embedding)
  tb7 <pB>                        TB7: print PASS | REJECT | HALT for a profile artifact
  tb7-vectors                     run TB7 on every vector that declares an expectation (N20/N21 included)
  s1-identity                     vendored S1 == frozen tag (tree id, SHA256SUMS, manifest digest)
  mustfail                        every P10S2TestsMustFail file must fail with its expected message
  gen-audit / check-audit         generate / verify P10S2/AxiomAudit.lean and its output
  gen-differential                write D1/D2 expected bytes from independent Python tooling (S1 p10tool JCS)
  leafspec                        every pB.leaf_encoding_spec_digest equals LeafEncodeSpecArtifactDigestV0(spec file)
  matrix                          result matrix (vector -> expected -> kernel-checked theorem)
Everything fails closed: any problem is a non-zero exit. No network. No `lake update`.
"""
import hashlib
import json
import pathlib
import re
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
MANIFEST_DIR = ROOT / "manifest"
VERIFIER_FILE = MANIFEST_DIR / "VerifierManifestS2aV0.json"
VECTOR_FILE = MANIFEST_DIR / "VectorManifestS2aV0.json"
S1_DIR = ROOT / "vendor" / "p10-underdetermination-lean-s1"

S1_TAG = "v0.1.0-s1-ratified"
S1_TAG_OBJECT = "7c3df437de454466b932a5d0dc889b3287c64e05"
S1_COMMIT = "e4db3747eaeeb1a07227bb9029f9a9c3b566cdb1"
S1_TREE = "6cdf48c29cd2207243912881c8f38c416ba2026a"
S1_MANIFEST_DIGEST = "06bf9129bf480c79ed5281ec2e944ac5613d1c340552ce5a415f5bf4c8965907"
LEAN_EXE_DIGEST = "9842f89b9a1874db969cc58933e4117c397338f795eb8febffeb79edd5272847"

# Manifest-covered files: the checker library and every acceptance-harness source/script.
HARNESS = ["scripts/s2a.py", "scripts/verify.sh", "scripts/install_toolchain.sh",
           "scripts/OleanImports.lean", "scripts/check_no_forbidden_scope.py",
           "scripts/check_env.py", "requirements.lock"]
LEAF_SPEC = "profile/LeafEncodeV0_SPEC.md"          # frozen, manifest-covered spec artifact (G6-B3)
POLICY_FILES = ["profile/AXIOM_POLICY.md", "profile/ACCEPTANCE_COMMAND.txt"]
VECTOR_DIRS = ["vectors", "P10S2Tests", "P10S2TestsMustFail"]
VECTOR_ROOT_FILES = ["P10S2Tests.lean"]

VERIFIER_KEYS = {
    "manifest_version", "lean_toolchain_identifier", "lean_toolchain_artifact_digest",
    "checker_source_tree_digest", "checker_source_files", "dependency_lock_digest",
    "build_manifest_digest", "checker_olean_digest_set", "axiom_policy_digest",
    "acceptance_command_digest", "frozen_dependencies"}
FROZEN_KEYS = {"s1_tag", "s1_peeled_commit", "s1_verifier_manifest_digest"}
HEX64 = re.compile(r"^[0-9a-f]{64}$")


def die(msg: str, code: int = 1):
    print(f"S2A FAIL: {msg}", file=sys.stderr)
    sys.exit(code)


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def sha_file(p) -> str:
    return sha((ROOT / p).read_bytes() if not isinstance(p, pathlib.Path) else p.read_bytes())


def canon(obj) -> bytes:
    """JCS-compatible for this schema: ASCII strings only, no numbers, keys sorted."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def checker_sources():
    return ["P10S2.lean"] + sorted(str(p.relative_to(ROOT)) for p in (ROOT / "P10S2").glob("*.lean")) \
        + HARNESS + [LEAF_SPEC]


def olean_paths():
    base = ROOT / ".lake" / "build" / "lib" / "lean"
    paths = [base / "P10S2.olean"] + sorted((base / "P10S2").glob("*.olean"))
    if not paths[0].is_file():
        die("checker .olean files missing: run `lake build P10S2` first")
    return [str(p.relative_to(ROOT)) for p in paths]


def lean_exe() -> pathlib.Path:
    p = shutil.which("lean")
    if not p:
        die("lean not on PATH")
    return pathlib.Path(p).resolve()


def verifier_manifest() -> dict:
    lean_digest = sha_file(lean_exe())
    if lean_digest != LEAN_EXE_DIGEST:
        die(f"lean executable digest {lean_digest} != pinned toolchain artifact {LEAN_EXE_DIGEST}")
    files = {p: sha_file(p) for p in checker_sources()}
    return {
        "manifest_version": "P10-S2a-VerifierManifest-v0",
        "lean_toolchain_identifier": "leanprover/lean4:v4.33.0",
        "lean_toolchain_artifact_digest": lean_digest,
        "checker_source_tree_digest": sha(canon(files)),
        "checker_source_files": files,
        "dependency_lock_digest": sha(canon({"lake-manifest.json": sha_file("lake-manifest.json"),
                                             "lean-toolchain": sha_file("lean-toolchain")})),
        "build_manifest_digest": sha(canon({"lakefile.toml": sha_file("lakefile.toml")})),
        "checker_olean_digest_set": {p: sha_file(p) for p in olean_paths()},
        "axiom_policy_digest": sha(canon({p: sha_file(p) for p in POLICY_FILES})),
        "acceptance_command_digest": sha_file("profile/ACCEPTANCE_COMMAND.txt"),
        "frozen_dependencies": {"s1_tag": S1_TAG, "s1_peeled_commit": S1_COMMIT,
                                "s1_verifier_manifest_digest": S1_MANIFEST_DIGEST},
    }


def schema_ok(obj) -> bool:
    """Exact schema of VerifierManifestS2aV0: no missing, extra or mistyped field."""
    if not isinstance(obj, dict) or set(obj) != VERIFIER_KEYS:
        return False
    for k in ("manifest_version", "lean_toolchain_identifier"):
        if not isinstance(obj[k], str):
            return False
    for k in ("lean_toolchain_artifact_digest", "checker_source_tree_digest", "dependency_lock_digest",
              "build_manifest_digest", "axiom_policy_digest", "acceptance_command_digest"):
        if not (isinstance(obj[k], str) and HEX64.match(obj[k])):
            return False
    for k in ("checker_source_files", "checker_olean_digest_set"):
        m = obj[k]
        if not (isinstance(m, dict) and m and all(isinstance(a, str) and isinstance(b, str)
                                                  and HEX64.match(b) for a, b in m.items())):
            return False
    fd = obj["frozen_dependencies"]
    if not (isinstance(fd, dict) and set(fd) == FROZEN_KEYS and all(isinstance(v, str) for v in fd.values())):
        return False
    return obj["checker_source_tree_digest"] == sha(canon(obj["checker_source_files"]))


def listing():
    files = {}
    for d in VECTOR_DIRS:
        for p in sorted((ROOT / d).rglob("*")):
            if p.is_file() and "__pycache__" not in p.parts and p.suffix != ".olean":
                files[str(p.relative_to(ROOT))] = sha_file(p)
    for f in VECTOR_ROOT_FILES:
        files[f] = sha_file(f)
    return files


def vector_manifest() -> dict:
    return {"manifest_version": "P10-S2a-VectorManifest-v0",
            "roots": sorted(VECTOR_DIRS + VECTOR_ROOT_FILES), "files": listing()}


def write_manifest(path, obj):
    MANIFEST_DIR.mkdir(exist_ok=True)
    path.write_bytes(canon(obj))
    print(sha(path.read_bytes()))


def read_canonical(path):
    b = path.read_bytes()
    obj = json.loads(b)
    if canon(obj) != b:
        die(f"{path.name} is not canonical JSON")
    return obj, b


def cmd_gen_verifier():
    obj = verifier_manifest()
    assert schema_ok(obj)
    write_manifest(VERIFIER_FILE, obj)


def cmd_check_verifier():
    if not VERIFIER_FILE.is_file():
        die("VerifierManifestS2aV0.json missing", 3)
    _, b = read_canonical(VERIFIER_FILE)
    now = canon(verifier_manifest())
    if b != now:
        old, new = json.loads(b), json.loads(now)
        diff = [k for k in new if old.get(k) != new[k]]
        die(f"running build differs from committed VerifierManifestS2aV0 (fields: {diff})")
    print(f"VerifierManifestS2aV0 matches the running build: {sha(b)}")


def cmd_gen_vector():
    write_manifest(VECTOR_FILE, vector_manifest())


def cmd_check_vector():
    if not VECTOR_FILE.is_file():
        die("VectorManifestS2aV0.json missing")
    obj, b = read_canonical(VECTOR_FILE)
    if set(obj) != {"manifest_version", "roots", "files"}:
        die("VectorManifestS2aV0 schema: unexpected fields")
    want, have = obj["files"], listing()
    if set(want) != set(have):
        die("vector/test file set differs from VectorManifestS2aV0: "
            f"unlisted={sorted(set(have) - set(want))} missing={sorted(set(want) - set(have))}")
    bad = [p for p in want if want[p] != have[p]]
    if bad:
        die(f"vector/test file digests differ: {bad}")
    if canon(vector_manifest()) != b:
        die("VectorManifestS2aV0 is stale")
    print(f"VectorManifestS2aV0: {len(want)} files, exact set and digests match: {sha(b)}")


def cmd_partition():
    vdig = sha(VECTOR_FILE.read_bytes()) if VECTOR_FILE.is_file() else None
    mdig = sha(VERIFIER_FILE.read_bytes())
    covered = checker_sources()
    # (1) source level: covered Lean modules import only covered P10S2.* or frozen S1 P10.*
    for p in covered:
        if not p.endswith(".lean") or p.startswith("scripts/"):
            continue
        for m in re.findall(r"(?m)^import\s+(\S+)", (ROOT / p).read_text()):
            if m.startswith("P10S2Tests") or not (m.startswith("P10S2") or m.startswith("P10.")):
                die(f"partition: covered source {p} imports {m}")
    # (2) .olean level: no covered .olean imports a test-library module
    out = subprocess.run(["lake", "env", "lean", "--run", "scripts/OleanImports.lean", *olean_paths()],
                         cwd=ROOT, capture_output=True, text=True)
    if out.returncode != 0:
        die(f"OleanImports failed: {out.stderr}")
    for line in out.stdout.strip().splitlines():
        path, imports = line.split("\t")
        for m in imports.split():
            if m.startswith("P10S2Tests") or not (m in ("Init", "Lean") or m.startswith("P10S2")
                                                  or m.startswith("P10.")):
                die(f"partition: covered olean {path} imports {m}")
    # (3) no covered file embeds a manifest digest (hex or raw)
    needles = [mdig.encode(), bytes.fromhex(mdig)]
    if vdig:
        needles += [vdig.encode(), bytes.fromhex(vdig)]
    for p in covered + olean_paths():
        data = (ROOT / p).read_bytes()
        for n in needles:
            if n in data:
                die(f"partition: {p} embeds a manifest digest")
    # (4) the vector-manifest digest appears in no pB and not in the verifier manifest
    if vdig:
        if vdig.encode() in VERIFIER_FILE.read_bytes():
            die("partition: verifier manifest mentions the vector-manifest digest")
        for p in (ROOT / "vectors").rglob("pB*.json"):
            if vdig.encode() in p.read_bytes():
                die(f"partition: {p} mentions the vector-manifest digest")
    print(f"partition rule holds ({len(covered)} covered sources, {len(olean_paths())} .olean files)")


def tb7(pbytes: bytes) -> str:
    """TB7: resolve pB.verifier_manifest_ref, recompute the running build's manifest, compare."""
    try:
        j = json.loads(pbytes)
        md, ref = j["verifier_manifest_digest"], j["verifier_manifest_ref"]
    except Exception:
        return "REJECT"
    if not (isinstance(md, str) and isinstance(ref, str)) or "/" in ref or ".." in ref:
        return "REJECT"
    target = MANIFEST_DIR / ref
    if not target.is_file():
        return "HALT"
    resolved = target.read_bytes()
    try:
        obj = json.loads(resolved)
    except Exception:
        return "REJECT"
    if canon(obj) != resolved or not schema_ok(obj):
        return "REJECT"
    running = sha(canon(verifier_manifest()))
    return "PASS" if md == sha(resolved) == running else "REJECT"


def cmd_tb7(path):
    print(tb7(pathlib.Path(path).read_bytes()))


def cmd_tb7_vectors():
    n = 0
    for exp in sorted((ROOT / "vectors").glob("*/expected.txt")):
        fields = dict(l.split(": ", 1) for l in exp.read_text().splitlines() if ": " in l)
        want = fields.get("tb7", "-")
        if want == "-":
            continue
        got = tb7((exp.parent / "pB.json").read_bytes())
        print(f"  TB7 {fields['id']}: expected {want}, got {got}")
        if got != want:
            die(f"TB7 harness result for {fields['id']} differs from the preregistered outcome")
        n += 1
    if n < 4:
        die("TB7 harness exercised fewer than P1, P2, N20, N21")
    print(f"TB7 harness: {n} vectors, all as preregistered")


def cmd_s1_identity():
    sums = (S1_DIR / "SHA256SUMS").read_text().splitlines()
    listed = {}
    for l in sums:
        d, p = l.split("  ", 1)
        listed[p] = d
    actual = {}
    for p in sorted(S1_DIR.rglob("*")):
        rel = str(p.relative_to(S1_DIR))
        if p.is_file() and not rel.startswith((".lake/", ".git/")) and rel != "SHA256SUMS" \
                and "__pycache__" not in p.parts:
            actual[rel] = sha(p.read_bytes())
    if set(actual) != set(listed):
        die(f"vendored S1 file set differs from its SHA256SUMS: {sorted(set(actual) ^ set(listed))}")
    bad = [p for p in listed if listed[p] != actual[p]]
    if bad:
        die(f"vendored S1 files differ from its SHA256SUMS: {bad}")
    mdg = sha((S1_DIR / "manifest" / "VerifierManifestS1.json").read_bytes())
    if mdg != S1_MANIFEST_DIGEST:
        die(f"vendored S1 verifier manifest digest {mdg} != {S1_MANIFEST_DIGEST}")
    if (ROOT / "vendor" / "S1_GIT_TREE").read_text().strip() != S1_TREE:
        die("vendor/S1_GIT_TREE does not record the tag's git tree id")
    if shutil.which("git"):
        import tempfile, os
        with tempfile.TemporaryDirectory() as t:
            env = dict(os.environ, GIT_DIR=t + "/g", GIT_WORK_TREE=str(S1_DIR))
            subprocess.run(["git", "init", "--bare", "-q", t + "/g"], check=True, env={**os.environ})
            subprocess.run(["git", "add", "-A", "-f", "--", ".", ":(exclude).lake"], check=True, env=env, cwd=S1_DIR,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            tree = subprocess.run(["git", "write-tree"], check=True, env=env, cwd=S1_DIR,
                                  capture_output=True, text=True).stdout.strip()
        if tree != S1_TREE:
            die(f"vendored S1 git tree id {tree} != tag tree {S1_TREE}")
    print(f"vendored S1 == {S1_TAG} (tag object {S1_TAG_OBJECT[:8]}, commit {S1_COMMIT[:8]}, "
          f"tree {S1_TREE[:8]}, manifest {S1_MANIFEST_DIGEST[:8]})")


MUSTFAIL = {
    # the false `hCov` is refuted either by the elaborator's `decide` ("is false") or by the kernel
    # (`decide +kernel` application type mismatch), depending on how early the checker rejects
    "N0_e2e.lean": ["cov inst pB T = CoverageOutcome.accept", ("is false", "(kernel) application type mismatch")],
    "N11_e2e.lean": ["cov inst pB T = CoverageOutcome.accept", ("is false", "(kernel) application type mismatch")],
    "no_hCov.lean": ["function type", "coverageCheck"],
    "no_hFaithful.lean": ["function type", "TranscriptFaithful"],
}


def cmd_mustfail():
    files = sorted(p.name for p in (ROOT / "P10S2TestsMustFail").glob("*.lean"))
    if files != sorted(MUSTFAIL):
        die(f"must-fail file set {files} != expected {sorted(MUSTFAIL)}")
    for name, frags in MUSTFAIL.items():
        r = subprocess.run(["lake", "env", "lean", f"P10S2TestsMustFail/{name}"], cwd=ROOT,
                           capture_output=True, text=True)
        out = r.stdout + r.stderr
        if r.returncode == 0:
            die(f"must-fail file {name} COMPILED (the composition theorem is unsound)")
        miss = [f for f in frags
                if not (any(a in out for a in f) if isinstance(f, tuple) else f in out)]
        if miss:
            die(f"must-fail file {name} failed for an unexpected reason (missing {miss}):\n{out[:800]}")
        print(f"  must-fail {name}: rejected as expected")
    print("must-fail files: all rejected for the expected reason")


def audit_text():
    names = subprocess.run([sys.executable, "scripts/check_no_forbidden_scope.py", "--list-theorems"],
                           cwd=ROOT, capture_output=True, text=True, check=True).stdout.split()
    head = ("import P10S2.Composition\n\n/-!\n# Axiom audit (GENERATED by `scripts/s2a.py gen-audit`)\n\n"
            "One `#print axioms` line per non-private theorem of the checker library. The acceptance\n"
            "command requires this file to be exactly up to date and every line to report only the\n"
            "permitted axioms of `profile/AXIOM_POLICY.md`.\n-/\n\n")
    return head + "".join(f"#print axioms {n}\n" for n in names), names


def cmd_gen_audit():
    text, names = audit_text()
    (ROOT / "P10S2" / "AxiomAudit.lean").write_text(text)
    print(f"wrote {len(names)} audit lines")


def cmd_check_audit():
    text, names = audit_text()
    if (ROOT / "P10S2" / "AxiomAudit.lean").read_text() != text:
        die("P10S2/AxiomAudit.lean is not exactly the current theorem inventory")
    r = subprocess.run(["lake", "env", "lean", "P10S2/AxiomAudit.lean"], cwd=ROOT,
                       capture_output=True, text=True)
    if r.returncode != 0:
        die(f"axiom audit failed to run: {r.stderr}")
    lines = [l for l in r.stdout.splitlines() if l.strip()]
    if len(lines) != len(names):
        die(f"axiom audit printed {len(lines)} lines for {len(names)} theorems")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for l, n in zip(lines, names):
        if "does not depend on any axioms" in l:
            continue
        m = re.match(r"'(.+)' depends on axioms: \[(.*)\]$", l)
        if not m or m.group(1) != n:
            die(f"unparsable audit line: {l}")
        used = {a.strip() for a in m.group(2).split(",")}
        if not used <= allowed:
            die(f"{n} depends on non-permitted axioms {sorted(used - allowed)}")
    print(f"axiom audit: {len(names)} theorems, only permitted axioms")
    return r.stdout


def leaf_spec_digest() -> str:
    """LeafEncodeSpecArtifactDigestV0: SHA-256 over two fixed prefixes and the raw file bytes (no JCS)."""
    return sha(b"P10-LeafEncodeSpecArtifact-v0:" + b"text-markdown-utf-8-v0:" + (ROOT / LEAF_SPEC).read_bytes())


def cmd_gen_differential():
    sys.path.insert(0, str(S1_DIR / "scripts"))
    import p10tool  # frozen S1 tooling: jcs()
    def d(obj):
        return bytes.fromhex(sha(p10tool.jcs(obj)))
    for name, data in (("D1/claim_digest.bin", d({"claim": "secondBit"})),
                       ("D1/evidence_digest.bin", d({"evidence": "f0s0"})),
                       ("D2/spec_digest.bin", bytes.fromhex(leaf_spec_digest()))):
        path = ROOT / "vectors" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    print("differential vectors written")


def cmd_leafspec():
    want, n = leaf_spec_digest(), 0
    for p in sorted((ROOT / "vectors").glob("*/pB.json")):
        try:
            got = json.loads(p.read_bytes())["leaf_encoding_spec_digest"]
        except Exception:
            continue
        if got != want:
            die(f"{p}: leaf_encoding_spec_digest {got} != {want}")
        n += 1
    if n < 10:
        die("leafspec: too few pB files checked")
    if (ROOT / "vectors/D2/spec_digest.bin").read_bytes().hex() != want:
        die("D2 expected bytes differ from the recomputed spec digest")
    print(f"leaf spec digest {want} matches {n} pB files and D2")


def cmd_matrix():
    rows = []
    for exp in sorted((ROOT / "vectors").glob("*/expected.txt")):
        f = dict(l.split(": ", 1) for l in exp.read_text().splitlines() if ": " in l)
        vid = f["id"]
        mod = ROOT / "P10S2Tests" / f"V_{vid}.lean"
        olean = ROOT / ".lake" / "build" / "lib" / "lean" / "P10S2Tests" / f"V_{vid}.olean"
        diff = f["condition"] == "differential"
        if not mod.is_file() or ("theorem " not in mod.read_text() if diff
                                 else "theorem outcome" not in mod.read_text()):
            die(f"vector {vid} has no kernel-checked `outcome` theorem")
        if not olean.is_file():
            die(f"vector {vid}: test module not built")
        rows.append((vid, f["prereg"], f["condition"], f["lean"], f["tb7"], "kernel-checked"))
    w = [max(len(r[i]) for r in rows + [("id", "prereg", "cond", "expected (Lean)", "tb7", "status")])
         for i in range(6)]
    hdr = ("id", "prereg", "cond", "expected (Lean)", "tb7", "status")
    for r in [hdr] + rows:
        print("  " + "  ".join(c.ljust(w[i]) for i, c in enumerate(r)))
    need = {"P1", "P2", "P2x", "P3", "D1", "D2"} | {f"N{i}" for i in range(0, 37)}
    have = {r[0] for r in rows} | {re.sub(r"[a-z]$", "", r[0]) for r in rows}
    if not need <= have:
        die(f"missing preregistered vectors: {sorted(need - have)}")
    print(f"matrix: {len(rows)} vectors (all preregistered P1-P3, P2x, N0-N36c, D1 present)")


def main():
    cmds = {"gen-verifier": cmd_gen_verifier, "check-verifier": cmd_check_verifier,
            "gen-vector": cmd_gen_vector, "check-vector": cmd_check_vector,
            "partition": cmd_partition, "tb7-vectors": cmd_tb7_vectors,
            "s1-identity": cmd_s1_identity, "mustfail": cmd_mustfail,
            "gen-differential": cmd_gen_differential, "leafspec": cmd_leafspec,
            "gen-audit": cmd_gen_audit, "check-audit": cmd_check_audit, "matrix": cmd_matrix}
    if len(sys.argv) >= 2 and sys.argv[1] == "tb7" and len(sys.argv) == 3:
        return cmd_tb7(sys.argv[2])
    if len(sys.argv) != 2 or sys.argv[1] not in cmds:
        die(f"usage: s2a.py {{{'|'.join(cmds)}|tb7 <pB>}}", 2)
    cmds[sys.argv[1]]()


if __name__ == "__main__":
    main()
