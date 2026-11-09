from pathlib import Path
import hashlib,json,zipfile,re,datetime
D=Path(__file__).resolve().parents[1];S=D.parent/'expanded-corpus-r84'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest={str(p.relative_to(S)):sha(p) for p in sorted(S.rglob('*')) if p.is_file()}
before=json.loads((D/'receipts/input-before.json').read_text())
(D/'receipts/input-after.json').write_text(json.dumps(manifest,indent=2))
assert before==manifest,'Read-only lane changed'
with zipfile.ZipFile(S/'hierarchy-packet.zip') as z:
 entries=[]
 for i in z.infolist():
  p=Path(i.filename);assert not p.is_absolute() and '..' not in p.parts and ((i.external_attr>>16)&0o170000)!=0o120000 and i.file_size<1000000
  data=z.read(i);entries.append({'path':i.filename,'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
  assert data==(D/'extracted'/p).read_bytes()
assert (D/'extracted/lean/Hierarchy.lean').read_bytes()==(S/'lean/Hierarchy.lean').read_bytes()
source=(D/'extracted/lean/Hierarchy.lean').read_text()
banned=re.findall(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool)\b',source)
assert not banned,banned
log=(D/'logs/full-audit.log').read_text();assert len(re.findall(r'^DECL ',log,re.M))==101 and 'TOTAL 101' in log
assert 'UNSAFE true' not in log and 'AXIOM true' not in log
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'read_only_lane_unchanged':True,'input_files':len(manifest),'packet_sha256':sha(S/'hierarchy-packet.zip'),'entries':entries,'local_module_sha256':sha(D/'extracted/lean/Hierarchy.lean'),'audit_count':101,'forbidden_source_tokens':banned,'local_rebuild':{n:json.loads((D/'logs'/f'{n}.receipt.json').read_text()) for n in ['strict-build','full-audit','leanchecker','sanity']}}
(D/'receipts/artifact-verification.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
