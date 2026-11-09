import base64
import gzip
import hashlib
import json
from pathlib import Path
import zipfile

base = Path(__file__).resolve().parent
data = json.loads((base / 'proof-sources.json').read_text())
parts = []
group = {}
size = 0
for name, encoded in data['files'].items():
    if group and size + len(encoded) > 8 * 1024 * 1024:
        parts.append(group)
        group, size = {}, 0
    group[name] = encoded
    size += len(encoded)
if group:
    parts.append(group)
paths = []
rebuilt = {}
for i, group in enumerate(parts, 1):
    path = base / f'proof-sources-part-{i:02d}.json'
    content = {k: v for k, v in data.items() if k != 'files'}
    content.update(part=i, part_count=len(parts), files=group)
    path.write_text(json.dumps(content, separators=(',', ':')) + '\n')
    assert path.stat().st_size < 50 * 1024 * 1024
    paths.append(path)
    rebuilt.update(json.loads(path.read_text())['files'])
assert rebuilt == data['files']
with zipfile.ZipFile(base / data['original_archive_name']) as archive:
    assert archive.testzip() is None
    names = [n for n in archive.namelist() if not n.endswith('/')]
    assert set(names) == set(rebuilt)
    for name in names:
        assert archive.read(name) == gzip.decompress(base64.b64decode(rebuilt[name]))
extractor = base / 'extract_sources.py'
extractor.write_text('''import json, base64, gzip
from pathlib import Path
base = Path(__file__).resolve().parent
parts = sorted(base.glob("proof-sources-part-*.json"))
assert parts, "Download all proof-sources-part-*.json attachments first"
data = [json.loads(p.read_text()) for p in parts]
assert len(data) == data[0]["part_count"]
assert [d["part"] for d in data] == list(range(1, len(data) + 1))
assert len({d["original_archive_sha256"] for d in data}) == 1
out = Path("extracted-proof-sources")
out.mkdir(exist_ok=False)
seen = set()
for part in data:
    for name, encoded in part["files"].items():
        rel = Path(name)
        assert not rel.is_absolute() and ".." not in rel.parts and name not in seen
        seen.add(name)
        target = out / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(gzip.decompress(base64.b64decode(encoded)))
print(out.resolve())
''')
paths.append(extractor)
manifest_path = base.parent / 'submission-manifest.json'
manifest = json.loads(manifest_path.read_text())
paper = next(p for p in manifest['papers'] if p['id'] == '333709')
paper['attachments'] = [str(p) for p in paths]
paper['attachment_sha256'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
paper['comments'] = 'Submitted by Myeongjin Kang. Related MathDB problem 333709. Proof sources are attached as proof-sources-part-01.json through proof-sources-part-' + f'{len(parts):02d}' + '.json (gzip-compressed, base64-encoded file contents); extract_sources.py reconstructs all archived files. Original archive SHA-256: ' + data['original_archive_sha256'] + '.'
paper['attachment_split_verification'] = {'file_count': len(rebuilt), 'parts': len(parts), 'all_bytes_match_original_zip': True}
manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'file_count': len(rebuilt), 'attachments': [{'name': p.name, 'bytes': p.stat().st_size} for p in paths]}))
