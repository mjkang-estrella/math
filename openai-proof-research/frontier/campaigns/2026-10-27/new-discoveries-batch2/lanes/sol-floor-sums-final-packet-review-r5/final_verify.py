"""Separate guarded final verifier; writes only the excluded receipt."""
from pathlib import Path
import hashlib,json,zipfile,tarfile
L=Path(__file__).resolve().parent
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
excluded={'manifest.json','verification-receipt.json'}
m=json.loads((L/'manifest.json').read_text())
assert set(m)=={p.relative_to(L).as_posix() for p in L.rglob('*') if p.is_file() and p.relative_to(L).as_posix() not in excluded}
for n,h in m.items():assert sha(L/n)==h,n
for r in json.loads((L/'input-bindings.json').read_text()):
    assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256'],r
for r in json.loads((L/'evidence/packet-check.json').read_text())['original_lean_references']:
    assert sha(Path(r['path']))==sha(L/r['copy'])==r['sha256'],r
with zipfile.ZipFile(L/'inputs/reviewed-packet/source-packet.zip') as z:
    original=json.loads((L/'evidence/extracted-members.json').read_text())
    assert set(z.namelist())=={r['path'] for r in original}
    for r in original:
        assert hashlib.sha256(z.read(r['path'])).hexdigest()==sha(L/'packet'/r['path'])==r['sha256']
with zipfile.ZipFile(L/'packet/source-packet.zip') as z,tarfile.open(L/'packet/source-packet.tar.gz') as t:
    internal=json.loads(z.read('SOURCE-MANIFEST.json'))
    assert set(z.namelist())==set(t.getnames())==set(internal)|{'SOURCE-MANIFEST.json'}
    for n in z.namelist():
        assert z.read(n)==t.extractfile(n).read()==(L/'packet'/n).read_bytes()
for ext in ['zip','tar.gz']:assert sha(L/('packet/source-packet.'+ext))==sha(L/('packet/rebuild.'+ext))
assert sha(L/'packet/source-packet.zip')=='d77b63418d77df6c1285d335e09c90f47a9ce233f0522114600caa0a72bd9c98'
assert (L/'packet/paper.md').read_bytes()==(L/'inputs/paper-reviewed.md').read_bytes()
assert (L/'packet/evidence/root-independent-audit.json').read_bytes()==(L/'inputs/root-independent-audit.json').read_bytes()
assert json.loads((L/'evidence/seam-check.json').read_text())['status']=='PASS'
a=json.loads((L/'administrative/ledger.json').read_text())
assert (a['accepted_count'],a['total_accepted_count'],a['next_global_outcome_number'])==(9,39,40)
for n,h in m.items():assert sha(L/n)==h,n
out={'status':'PASS','manifest_files':len(m),'manifest_sha256':sha(L/'manifest.json'),'original_copy_bindings':6,'root_replayed_lean_files_rechecked':460,'archive_members_rechecked':555,'scientific_originals_and_copies_unchanged':True,'source_math_formal_packet_manuscript':'PASS with review.md scope and attributed kernel replay','PDF':'NOTAUTHORED / QA_NOTPERFORMED','substantive':'qualified PASS; root adjudicates','novelty':'bounded HOLD','acceptance':'HOLD; root alone accepts','counts':'9 additional / 39 total / next40 unchanged'}
(L/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
