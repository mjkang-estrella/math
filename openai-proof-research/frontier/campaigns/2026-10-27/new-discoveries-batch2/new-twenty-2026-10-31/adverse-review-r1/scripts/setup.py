from pathlib import Path
import hashlib,json,zipfile
r=Path.cwd(); p=r.parent
paths=[]
for lane in ['adverse-formal-r2','adverse-formal-r1']:
 paths += [x for x in (p/lane).rglob('*') if x.is_file()]
paths += [p/'adverse-root-ruling-r1.json']
c=p/'expanded-corpus-r101'
paths += [c/'outputs/LATIN36-ORDINARY-PROOF.md',c/'latin36-certificate.json',c/'raw/381433.jsonl']+list((c/'sources').glob('381433.*'))
# certificate lives in outputs in some corpus layouts
paths += list(c.rglob('latin36-certificate.json'))
manifest={str(x):hashlib.sha256(x.read_bytes()).hexdigest() for x in sorted(set(paths)) if x.is_file()}
(r/'receipts/input-before.json').write_text(json.dumps(manifest,indent=2))
z=p/'adverse-formal-r2/adverse-381433-source.zip'
assert manifest[str(z)]=='aefc4cc7ea17aa2ae0797a739ee8ec40b56097c281e0435f403c4e93de47420b'
out=r/'extracted';out.mkdir()
with zipfile.ZipFile(z) as f:
 for n in f.infolist():
  q=Path(n.filename)
  assert not q.is_absolute() and '..' not in q.parts and ((n.external_attr>>16)&0o170000)!=0o120000
  assert q.suffix not in ['.olean','.so']
 f.extractall(out)
(r/'receipts/extraction.json').write_text(json.dumps({'sha256':manifest[str(z)],'entries':len(f.infolist()),'safe':True}))
print('hashed',len(manifest),'files')
