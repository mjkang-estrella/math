from pathlib import Path,PurePosixPath
import shutil,zipfile,json,hashlib
O=Path(__file__).resolve().parent; B=O.parent; S=B/'fresh-corpus-r15'
def cp(a,b):
 p=O/b;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(a,p)
cp(S/'proof-packet.zip','original/proof-packet.zip'); cp(S/'lean/FractionalDefect.lean','proof/FractionalDefect.lean')
with zipfile.ZipFile(S/'proof-packet.zip') as z:
 seen=set(); members=[]
 for i in z.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename and i.filename not in seen and i.file_size<10_000_000 and (i.external_attr>>16)&0o170000 !=0o120000
  seen.add(i.filename); data=z.read(i); dest=O/'work/fresh'/i.filename;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
  members.append({'path':i.filename,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)})
  if i.filename not in ['FractionalDefect.lean']: cp(dest,'proof/'+i.filename)
(O/'extraction.json').write_text(json.dumps(members,indent=2)+'\n')
assert (O/'work/fresh/FractionalDefect.lean').read_bytes()==(S/'lean/FractionalDefect.lean').read_bytes()
for lane in ['fractional-defect-significance-review-r1','fractional-defect-fidelity-review-r1']:
 for name in ['REVIEW.md','review.json','input-bindings.json']:
  cp(B/lane/name,'reviews/'+lane+'/'+name)
for name in ['AuditAll.lean','declaration-audit.json','dependency-revisions.json','literal-check.json','package-integrity.json','source-scan.json','audit-all.log','independent-arithmetic.py','independent-arithmetic.json']:
 cp(B/'fractional-defect-fidelity-review-r1'/name,'reviews/fidelity-evidence/'+name)
for name in ['new-http-receipts.json','companion-receipt.json','search-log.json','seriesParallel.pdf','seriesParallel.txt','siamTalk14.pdf','siamTalk14.txt','GoddardCV.pdf','GoddardCV.txt','arxiv-current.html']:
 cp(B/'fractional-defect-significance-review-r1'/name,'sources/review-supplement/'+name)
for name in ['335230-1702.01442v1.pdf','335230-1702.01442v1.txt','335230-1702.01442v2.pdf','335230-1702.01442v2.txt','335230-author-preprint.pdf','335230-author-preprint.txt','http-log.json','arxiv-335230-abs.html']:
 cp(S/'sources'/name,'sources/'+name)
for name in ['literal-records.json','literal-provenance.json','registry-reuse.json','historical-exact-hits.json','artifact-hashes.json']:
 cp(S/name,'provenance/'+name)
x=next(x for x in json.loads((S/'literal-provenance.json').read_text()) if x['id']==335230)
raw=Path(x['chunk']).read_bytes(); line=raw.splitlines(keepends=True)[x['line_number']-1]
assert hashlib.sha256(raw).hexdigest()==x['chunk_sha256'];assert hashlib.sha256(line).hexdigest()==x['raw_line_sha256']
r=next(x for x in json.loads((S/'literal-records.json').read_text()) if x['mathdb_id']==335230)
assert json.loads(line)==r==json.loads((O/'proof/mathdb-335230.json').read_text())
(O/'provenance/literal-335230-line.jsonl').write_bytes(line)
(O/'literal-verification.json').write_text(json.dumps({'pass':True,'provenance':x,'packet_equals_literal':True},indent=2)+'\n')
