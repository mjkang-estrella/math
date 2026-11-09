"""Offline dossier preparation. Run with python3 -I, from this directory."""
import os, resource, pathlib, hashlib, json, shutil, tarfile, re, itertools
resource.setrlimit(resource.RLIMIT_CPU, (120,120))
resource.setrlimit(resource.RLIMIT_AS, (1900000000,1900000000))
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
D = pathlib.Path(__file__).resolve().parent
B = D.parent
H = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def save(p, obj):
    (D/p).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
before = json.loads((D/'inputs-before.json').read_text())
assert all(H(B/p)==h for p,h in before.items())
# Preserve the relevant primary sources and all their existing access receipts.
paths = ['toroidal-root-ruling-r1.json']
for name in ['SUMMARY.md','CANDIDATE-369421.md','results.json','lean-packet.tar.gz']:
    paths.append('expanded-corpus-r158/'+name)
for name in ['369421.raw.jsonl','369421.abs','369421.html','369421.txt','grid.pdf','grid-pdf.txt','grid-publication','kitaev-publications','broere-thesis.pdf','broere-thesis.txt','product-cube.pdf','product-cube.abs','product-cube.txt','chessboard.html','chessboard.txt']:
    paths.append('expanded-corpus-r158/sources/'+name)
for p in (B/'expanded-corpus-r158/outputs').iterdir():
    if 'receipt' in p.name or p.name in ['pair-certificate.json','lean-sha256.txt','grid-3-5-witness.json']:
        paths.append(str(p.relative_to(B)))
for name in ['REVIEW.md','review.json','pair-check.json','toolchain.sha256']:
    paths.append('toroidal-review-r1/'+name)
for folder in ['downloads','scripts','logs']:
    paths += [str(p.relative_to(B)) for p in (B/'toroidal-review-r1'/folder).rglob('*') if p.is_file()]
for folder in ['logs','rootcheck','registries']:
    paths += [str(p.relative_to(B)) for p in (B/'toroidal-parent-final-r1'/folder).rglob('*') if p.is_file()]
for name in ['replay-result.json','registry-refresh.json','root-independent-check.txt','root-replay.out']:
    paths.append('toroidal-parent-final-r1/'+name)
for name in sorted(set(paths)):
    p=D/'evidence'/name
    p.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(B/name,p)
    assert H(p)==before[name]
save('copy-receipt.json',{p:before[p] for p in sorted(set(paths))})
shutil.copyfile(B/'expanded-corpus-r158/lean-packet.tar.gz',D/'lean-packet.tar.gz')
expected='9f16ff5afa9a23b693443c0916507a8103bef5f23e431ca6c39e8cb4e7318200'
assert H(D/'lean-packet.tar.gz')==expected
extract=D/'packet-safe-extracted'
assert not extract.exists()
extract.mkdir()
with tarfile.open(D/'lean-packet.tar.gz','r:gz') as tf:
    members=tf.getmembers()
    assert len(members)==3
    assert {m.name for m in members}=={'Definitions.lean','Witness.lean','Audit.lean'}
    for m in members:
        assert m.isfile() and not m.issym() and not m.islnk()
        assert 0<m.size<1000000
        data=tf.extractfile(m).read()
        with (extract/m.name).open('xb') as f: f.write(data)
save('safe-extraction.json',{'status':'PASS','packet_sha256':expected,'policy':'exact flat allowlist; regular files only; bounded sizes; exclusive creation in fresh directory; no code execution','files':{p.name:H(p) for p in extract.iterdir()}})
raw=D/'evidence/expanded-corpus-r158/sources/369421.raw.jsonl'
assert len(raw.read_bytes().splitlines())==1
save('mathdb-raw-receipt.json',{'file':str(raw.relative_to(D)),'sha256_including_newline':H(raw),'bytes':raw.stat().st_size,'mathdb_id':json.loads(raw.read_text())['mathdb_id']})
print('Prepared byte-identical sources and packet; safe extraction PASS')
