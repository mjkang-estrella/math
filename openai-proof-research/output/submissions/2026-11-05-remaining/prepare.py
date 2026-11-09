"""Prepare accepted, locally unsubmitted papers; performs no network mutations."""
from pathlib import Path
import base64
import gzip
import hashlib
import json
import shutil
import zipfile

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
CAMPAIGN = ROOT / 'frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31'

def sha(data):
    return hashlib.sha256(data).hexdigest()

submitted = set()
prior_manifests = []
for path in OUT.parent.glob('*/submission-manifest.json'):
    if path.parent == OUT:
        continue
    data = json.loads(path.read_text())
    prior_manifests.append({'path': str(path), 'sha256': sha(path.read_bytes())})
    for row in data.get('papers', []):
        if row.get('status') == 'submitted' or row.get('mathdb_url'):
            submitted.add(str(row.get('id', row.get('mathdb_id'))))

rows = []
ledger = json.loads((CAMPAIGN / 'ledger.json').read_text())
for entry in ledger['accepted']:
    ident = str(entry['mathdb_id'])
    if ident in submitted:
        continue
    acceptance_path = CAMPAIGN / (entry.get('acceptance') or entry['file'])
    accepted = json.loads(acceptance_path.read_text())
    assert accepted['credit'] == 1
    dest = OUT / ident
    dest.mkdir(exist_ok=True)
    row = {'id': ident, 'title': accepted['title'], 'authors': 'Myeongjin Kang',
           'scope': accepted['scope'], 'status': 'prepared_not_submitted',
           'acceptance_path': str(acceptance_path),
           'acceptance_sha256': sha(acceptance_path.read_bytes())}
    for key in ['paper', 'proof_packet']:
        src = CAMPAIGN / accepted[key]
        raw = src.read_bytes()
        assert sha(raw) == accepted['sha256'][key], (ident, key)
        target = dest / src.name
        shutil.copyfile(src, target)
        row[key] = str(target)
        row[key + '_sha256'] = sha(raw)
    files = {}
    with zipfile.ZipFile(row['proof_packet']) as archive:
        assert archive.testzip() is None
        for item in archive.infolist():
            if item.is_dir():
                continue
            name = Path(item.filename)
            assert not name.is_absolute() and '..' not in name.parts
            assert item.filename not in files
            raw = archive.read(item)
            encoded = base64.b64encode(gzip.compress(raw, mtime=0)).decode()
            assert gzip.decompress(base64.b64decode(encoded)) == raw
            files[item.filename] = encoded
    package = {'original_archive_name': Path(row['proof_packet']).name,
               'original_archive_sha256': row['proof_packet_sha256'],
               'encoding': 'gzip+base64', 'files': files}
    attachment = dest / 'proof-sources.json'
    attachment.write_text(json.dumps(package))
    extractor = dest / 'extract_sources.py'
    extractor.write_text('''import json, base64, gzip
from pathlib import Path
data = json.loads(Path(__file__).with_name("proof-sources.json").read_text())
out = Path("extracted-proof-sources")
out.mkdir(exist_ok=False)
for name, encoded in data["files"].items():
    rel = Path(name)
    assert not rel.is_absolute() and ".." not in rel.parts
    target = out / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(gzip.decompress(base64.b64decode(encoded)))
print(out.resolve())
''')
    row['attachments'] = [str(attachment), str(extractor)]
    row['attachment_sha256'] = {p.name: sha(p.read_bytes()) for p in [attachment, extractor]}
    row['archived_file_count'] = len(files)
    row['abstract'] = accepted['scope'] + '\n\nAI-assisted research preprint. The scoped main statement has a Lean certificate. Internal AI review is not external journal peer review; bounded prior-art searches do not certify worldwide priority. See the paper for exact qualifications and formalization limits.'
    row['comments'] = ('Submitted by Myeongjin Kang. Related MathDB problem ' + ident
        + '. Proof sources are attached as proof-sources.json (gzip-compressed, base64-encoded file contents); extract_sources.py reconstructs all archived files. Original archive SHA-256: '
        + row['proof_packet_sha256'] + '.')
    row['qualification_limits'] = {k: accepted.get(k, []) for k in ['remaining_literature_limits', 'trust_limits', 'not_claimed']}
    rows.append(row)
    print(ident, len(files), round(attachment.stat().st_size / 1048576, 2), 'MiB')

manifest = {'status': 'prepared_browser_unavailable', 'submitted_count': 0,
            'live_duplicate_check': 'pending; local prior manifests reconciled',
            'prior_manifests': prior_manifests, 'papers': rows}
(OUT / 'submission-manifest.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
lines = ['# Prepared MathDB submissions — 2026-11-05', '',
         f'{len(rows)} accepted papers with no local submission receipt. None submitted in this batch.', '',
         'All paper and proof archive hashes match acceptance records. All packaged source files round-trip byte-for-byte.',
         'Live duplicate check and upload remain pending because browser automation was unavailable.', '',
         '| Problem | Accepted paper | Status |', '|---|---|---|']
for row in rows:
    lines.append(f"| {row['id']} | {row['title']} | Prepared, not submitted |")
(OUT / 'SUBMISSION-INDEX.md').write_text('\n'.join(lines) + '\n')
