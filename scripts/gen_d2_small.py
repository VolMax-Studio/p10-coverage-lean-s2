#!/usr/bin/env python3
"""Maintainer-only (not part of the acceptance command): expected bytes for the small kernel
differential vectors of D2, computed independently of Lean with hashlib.
LeafEncodeSpecArtifactDigestV0(f) = SHA-256("P10-LeafEncodeSpecArtifact-v0:" ++ "text-markdown-utf-8-v0:" ++ f)."""
import hashlib
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
PREFIX = b"P10-LeafEncodeSpecArtifact-v0:" + b"text-markdown-utf-8-v0:"
out = ROOT / "vectors" / "D2"
out.mkdir(parents=True, exist_ok=True)
(out / "empty_digest.bin").write_bytes(hashlib.sha256(PREFIX + b"").digest())
(out / "small_digest.bin").write_bytes(hashlib.sha256(PREFIX + b"# LeafEncodeV0\n").digest())
print("D2 small differential bytes written")
