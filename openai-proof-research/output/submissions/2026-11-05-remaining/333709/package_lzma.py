import base64
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import zipfile

base = Path(__file__).resolve().parent
compressed = (base / 'proof-sources.tar.xz').read_bytes()
encoded = base64.b64encode(compressed).decode('ascii')
chunks = [encoded[i:i + 8_000_000] for i in range(0, len(encoded), 8_000_000)]
assert len(chunks) <= 3
original_hash = hashlib.sha256((base / 'source-only.zip').read_bytes()).hexdigest()
paths = []
for i, chunk in enumerate(chunks, 1):
    path = base / f'proof-sources-part-{i:02d}.json'
    path.write_text(json.dumps({'encoding': 'tar+xz+base64-chunks', 'part': i, 'part_count': len(chunks),
        'original_archive_sha256': original_hash,
        'compressed_payload_sha256': hashlib.sha256(compressed).hexdigest(), 'payload': chunk}) + '\n')
    assert path.stat().st_size < 10_000_000
    paths.append(path)
for i in range(len(chunks) + 1, 10):
    (base / f'proof-sources-part-{i:02d}.json').unlink(missing_ok=True)
extractor = base / 'extract_sources.py'
extractor.write_text('''import base64, hashlib, io, json, tarfile
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
''')
paths.append(extractor)
with tempfile.TemporaryDirectory() as temp:
    subprocess.run(['python', str(extractor)], cwd=temp, check=True)
    out = Path(temp) / 'extracted-proof-sources'
    with zipfile.ZipFile(base / 'source-only.zip') as archive:
        names = [n for n in archive.namelist() if not n.endswith('/')]
        assert {str(p.relative_to(out)) for p in out.rglob('*') if p.is_file()} == set(names)
        assert all((out / n).read_bytes() == archive.read(n) for n in names)
manifest_path = base.parent / 'submission-manifest.json'
manifest = json.loads(manifest_path.read_text())
paper = next(p for p in manifest['papers'] if p['id'] == '333709')
paper['attachments'] = [str(p) for p in paths]
paper['attachment_sha256'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
paper['comments'] = 'Submitted by Myeongjin Kang. Related MathDB problem 333709. Download all three proof-sources-part-01.json through proof-sources-part-03.json attachments and extract_sources.py together. Run the extractor to reconstruct all 848 archived files (tar+xz+base64 encoding). All extracted file bytes were compared with the accepted original archive. Original archive SHA-256: ' + original_hash + '.'
paper['attachment_split_verification'] = {'file_count': len(names), 'parts': len(chunks), 'encoding': 'tar+xz+base64-chunks', 'extractor_replayed': True, 'all_bytes_match_original_zip': True}
manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'verified_files': len(names), 'attachments': [{'name': p.name, 'bytes': p.stat().st_size} for p in paths]}))
