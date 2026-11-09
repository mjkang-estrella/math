from pathlib import Path
import hashlib,json,shutil,tarfile
P=Path(__file__).resolve().parents[1]; B=P.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=[]
for lane in ['expanded-corpus-r144','rainbow-review-r1']:
 files += sorted(p for p in (B/lane).rglob('*') if p.is_file())
files += [B/'rainbow-root-ruling-r1.json']
rows=[{'path':str(p.relative_to(B)),'sha256':sha(p),'bytes':p.stat().st_size} for p in files]
(P/'input-before.json').write_text(json.dumps(rows,indent=2)+'\n')
def copy(src,dst):
 d=P/dst; d.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(B/src,d)
for f in ['SUMMARY.md','PROOF.md','CERTIFICATES.md','ACCESS.md','results.json','extracted.json','lean-packet.tar.gz']:
 copy('expanded-corpus-r144/'+f, 'evidence/original/'+f if f!='lean-packet.tar.gz' else f)
for f in ['Base.lean','Semantics.lean','Final.lean','Certificates.lean','Audit.lean','MetadataAudit.lean']:
 copy('expanded-corpus-r144/'+f,'evidence/lean/'+f)
copy('expanded-corpus-r144/raw/346167.jsonl','mathdb-346167.jsonl')
for p in (B/'expanded-corpus-r144/sources').iterdir():
 if p.name.startswith(('2004.06285','1812.10034','2307.03964','weng2025','receipts')):
  copy(str(p.relative_to(B)),'sources/'+p.name)
for p in (B/'expanded-corpus-r144/outputs').glob('rainbow-*'): copy(str(p.relative_to(B)),'evidence/original/outputs/'+p.name)
for f in ['REVIEW.md','review.json','atlas.json','candidate.json','brute-candidate.json','extensions9.json','extensions10.json','download-manifest.json']:
 copy('rainbow-review-r1/'+f,'evidence/review/'+f)
for sub in ['downloads','scripts','logs']:
 for p in (B/'rainbow-review-r1'/sub).rglob('*'):
  if p.is_file(): copy(str(p.relative_to(B)),'evidence/review/'+str(p.relative_to(B/'rainbow-review-r1')))
copy('rainbow-root-ruling-r1.json','evidence/rainbow-root-ruling-r1.json')
assert sha(P/'lean-packet.tar.gz')=='038c7acfb665189952f706cfdf65de6d9bc5dc16c4a7af70f3b0832ec4c86057'
with tarfile.open(P/'lean-packet.tar.gz') as t:
 members=t.getmembers(); names=set()
 for m in members:
  q=Path(m.name)
  assert not q.is_absolute() and '..' not in q.parts and not m.issym() and not m.islnk() and (m.isfile() or m.isdir())
  assert m.name not in names; names.add(m.name)
 d=P/'safe-extraction'; d.mkdir(exist_ok=True)
 t.extractall(d,filter='data')
 checks=[{'name':m.name,'sha256':sha(d/m.name)} for m in members if m.isfile()]
 for m in members:
  if m.isfile(): assert hashlib.sha256(t.extractfile(m).read()).hexdigest()==sha(d/m.name)
(P/'safe-extraction-receipt.json').write_text(json.dumps({'safe':True,'lean_executed':False,'files':checks},indent=2)+'\n')
(P/'mathdb-346167.sha256').write_text(sha(P/'mathdb-346167.jsonl')+'  mathdb-346167.jsonl\n')
print('frozen files',len(rows),'safe packet files',len(checks))
