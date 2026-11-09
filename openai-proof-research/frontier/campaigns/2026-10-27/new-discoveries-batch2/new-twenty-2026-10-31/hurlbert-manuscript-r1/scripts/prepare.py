from pathlib import Path
import hashlib,json,shutil,zipfile,stat
D=Path(__file__).resolve().parents[1];P=D.parent
roots=['expanded-corpus-r234','hurlbert-review-r1','hurlbert-root-check-r1','hurlbert-formal-r1','hurlbert-parent-final-r1']
files=[P/'hurlbert-root-ruling-r1.json']
for root in roots:
 files += [p for p in (P/root).rglob('*') if p.is_file() and p.suffix not in ['.olean','.ok']]
hashes={str(p.relative_to(P)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(files))}
(D/'receipts/inputs-before.json').write_text(json.dumps(hashes,indent=2)+'\n')
# Preserve the read inputs, including primary bodies, access receipts and historical scripts as inert evidence.
for rel in hashes:
 target=D/'inputs'/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(P/rel,target)
shutil.copyfile(P/'hurlbert-formal-r1/proof-source.zip',D/'proof-source.zip')
assert hashlib.sha256((D/'proof-source.zip').read_bytes()).hexdigest()=='d695606abe9bdcd465c1b0de182bc8e9c202044720687c92adcd8ff7314192e6'
with zipfile.ZipFile(D/'proof-source.zip') as z:
 names=z.namelist();assert len(names)==len(set(names))==6
 assert set(names)=={'Hurlbert.lean','Endpoints.lean','Control.lean','Inventory.lean','AllAxioms.lean','module-order.txt'}
 assert sum(i.file_size for i in z.infolist())<1000000
 for i in z.infolist():
  assert not stat.S_ISLNK(i.external_attr>>16)
  assert not Path(i.filename).is_absolute() and '..' not in Path(i.filename).parts
  target=D/'safe-extracted'/i.filename;target.parent.mkdir(exist_ok=True);target.write_bytes(z.read(i))
(D/'receipts/safe-extraction.json').write_text(json.dumps(dict(pass_=True,members=names,executed=False,packet_sha256=hashlib.sha256((D/'proof-source.zip').read_bytes()).hexdigest()),indent=2)+'\n')
print('Frozen and copied',len(hashes),'inputs; packet safely extracted, no Lean run.')
