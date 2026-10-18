#!/usr/bin/env python3
"""Regression checks for standalone archive validation and repeat runs."""
from __future__ import annotations

import hashlib
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    archive = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "submission/current/complete-reproducibility.zip"
    with TemporaryDirectory(prefix="exact-hoeffding-bundle-test-") as directory:
        root = Path(directory)
        with ZipFile(archive) as bundle:
            bundle.extractall(root)
        def check(ok: bool, marker: str = "") -> None:
            result = subprocess.run([sys.executable, "checks/verify_reproducibility_bundle.py"],
                                    cwd=root, text=True, capture_output=True)
            output = result.stdout + result.stderr
            if (result.returncode == 0) != ok or marker not in output:
                raise AssertionError(output)
        check(True)
        cache = root / ".lake/build/lib/lean/Generated.olean"
        cache.parent.mkdir(parents=True)
        cache.write_bytes(b"generated Lake cache")
        check(True)
        unlisted = root / "unlisted.txt"
        unlisted.write_text("must be rejected")
        check(False, "unlisted.txt")
        unlisted.unlink()
        nested_cache = root / "checks/.lake/foreign.txt"
        nested_cache.parent.mkdir()
        nested_cache.write_text("only root .lake may be excluded")
        check(False, "checks/.lake/foreign.txt")
        nested_cache.unlink()
        source = root / "submission/current/manuscript.tex"
        original = source.read_bytes()
        source.write_bytes(original + b"\n% tampering\n")
        check(False, "checksum mismatch")
        source.write_bytes(original)
        audit = root / "formal_status/manuscript_concordance.md"
        original_audit = audit.read_bytes()
        import re
        text = re.sub(r"(the current PDF SHA-256 is `)[0-9a-f]{64}",
                      lambda m: m[1] + "0" * 64, original_audit.decode())
        audit.write_text(text)
        manifest = root / "SHA256SUMS.txt"
        original_manifest = manifest.read_bytes()
        rows = manifest.read_text().splitlines()
        name = audit.relative_to(root).as_posix()
        digest = hashlib.sha256(audit.read_bytes()).hexdigest()
        rows = [digest + "  " + name if row.endswith("  " + name) else row for row in rows]
        manifest.write_text("\n".join(rows) + "\n")
        check(False, "published PDF fingerprint mismatch")
        audit.write_bytes(original_audit)
        manifest.write_bytes(original_manifest)
        check(True)
    print("PASS: clean extraction, repeat run with Lake cache, unlisted files, source tampering, and stale PDF fingerprints")


if __name__ == "__main__":
    main()
