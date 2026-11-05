"""Provenance shared by compiled and explicitly unverified source reports."""
import datetime
import hashlib
import json
import os
import tempfile
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[2]


def source_fingerprint(root=PROJECT):
    files = [root / p for p in ("GSQG.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain")]
    files += sorted((root / "GSQG").rglob("*.lean"))
    files += sorted((root / "blueprint/src").rglob("*.tex"))
    files += sorted((root / "blueprint/tools").glob("*.lean"))
    digest = hashlib.sha256()
    for path in files:
        digest.update(str(path.relative_to(root)).encode())
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def report(declarations, source, fingerprint, root=PROJECT):
    return {"schema_version": 2, "metadata": {
        "source": source,
        "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
        "source_fingerprint": fingerprint,
        "toolchain": (root / "lean-toolchain").read_text().strip(),
        "root_module": "GSQG",
    }, "declarations": declarations}


def write_json(path, data):
    """Do not replace the previous report until the new JSON is complete."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, filename = tempfile.mkstemp(prefix=path.name + '.', suffix='.new', dir=path.parent)
    tmp = Path(filename)
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as stream:
            stream.write(json.dumps(data, indent=1, ensure_ascii=False) + "\n")
        tmp.chmod(0o644)
        tmp.replace(path)
    finally:
        tmp.unlink(missing_ok=True)


def unpack_status(data):
    if data.get("schema_version") == 2:
        return data["declarations"], data["metadata"]
    # Old reports cannot establish that the current sources were compiled.
    return data, {"source": "legacy", "checked_at": None}
