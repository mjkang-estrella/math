import base64, hashlib, io, json, tarfile
from pathlib import Path
base = Path(__file__).resolve().parent
parts = [json.loads(p.read_text()) for p in sorted(base.glob("proof-sources-part-*.json"))]
assert parts and len(parts) == parts[0]["part_count"], "Download every JSON part first"
assert [p["part"] for p in parts] == list(range(1, len(parts) + 1))
assert all(p["encoding"] == "tar+xz+base64-chunks" for p in parts)
assert len({p["original_archive_sha256"] for p in parts}) == 1
assert len({p["compressed_payload_sha256"] for p in parts}) == 1
data = base64.b64decode("".join(p["payload"] for p in parts), validate=True)
assert hashlib.sha256(data).hexdigest() == parts[0]["compressed_payload_sha256"]
out = Path("extracted-proof-sources")
out.mkdir(exist_ok=False)
seen = set()
with tarfile.open(fileobj=io.BytesIO(data), mode="r:xz") as archive:
    for member in archive:
        rel = Path(member.name)
        assert member.isfile() and not rel.is_absolute() and ".." not in rel.parts
        assert member.name not in seen
        seen.add(member.name)
        target = out / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(archive.extractfile(member).read())
print(out.resolve())
