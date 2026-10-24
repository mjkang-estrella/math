#!/usr/bin/env python3
"""Read-only artifact intake; no mathematical verdict or inherited reading."""
from pathlib import Path
import datetime,hashlib,json,os,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];A=C/'fresh-structural-discovery-r220';K=A/'packet';Q=K/'private'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'a5b12e373fb82bc0e32cb2c9edee112330e40012751841257ecf251f37ce9680','MANIFEST':'52322600b2109b42a198e7a3b51d42952fb0fd15a5666904dcd7eb7c82fdf023','REPORT':'5c6c04cb98ea1e883a51ae8854770dad04d060f110a83264ebc5ed4f0fd350f9'}
statement='4c71274685f1401193eccbc7c6997b56d1ca2db88fef14cba159d638260aa35d';proof='efd13b45cbf17c3620c6bedc00152b1deb42e7cd6f7d37898019ded5aa6b5775';verifier='c4055ca001ae3e298efee01e446855fcc438a26e60991d71cdd54536ac758075'
def observe(root):
 out={}
 for parent,dirs,files in os.walk(root,followlinks=False):
  for p in [Path(parent),*(Path(parent)/n for n in files)]:
   assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
   if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
   out[p.relative_to(root).as_posix()]=e
  assert all(not (Path(parent)/n).is_symlink() for n in dirs)
 return out
def run(root,a):
 return subprocess.run(['python3','-I','-B',str(K/'verify_packet.py'),'--root',str(root),'--manifest-sha256',a['MANIFEST'],'--final-sha256',a['FINAL'],'--report-sha256',a['REPORT']],capture_output=True,text=True)
before=observe(A)
assert sha((K/'STATEMENT.md').read_bytes())==statement and sha((K/'PROOF.md').read_bytes())==proof and sha((K/'verify_packet.py').read_bytes())==verifier
v=run(A,anchors);assert v.returncode==0,(v.stdout,v.stderr)
m=read(A/'MANIFEST.json');assert m['scope_sha256']==statement
for e in m['files']:
 b=(K/e['path']).read_bytes();original=A/e['path']
 if e['path'].startswith('private/code/') or e['path']=='private/guards.json':original=A/Path(e['path']).name
 assert b==original.read_bytes()
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']};assert len(tree)==13223
prefix='preprints/The-metric-Blaschke-theorem-September-23-2026'
assert read(Q/'tree-selection.json')==[e for e in json.loads(tb)['tree'] if e['path']==prefix or e['path'].startswith(prefix+'/')]
source=read(Q/'authentication.json');assert len(source)==16
for e in source:
 b=(K/e['local']).read_bytes();t=tree[e['path']]
 assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha'] and e['mode']==t['mode']
logs=[json.loads(s) for s in (Q/'reads.jsonl').read_text().splitlines()]
for e in logs:
 p=K/e['path'];assert p.resolve().is_relative_to(K);b=p.read_bytes();lines=b.splitlines(keepends=True);lo,hi=e['bytes'];first,last=e['lines']
 assert lo==sum(map(len,lines[:first-1])) and hi==sum(map(len,lines[:last])) and sha(b[lo:hi])==e['sha256']
pdfs=0;errors=[]
for e in read(Q/'primary/access.json'):
 if not e.get('pdf'):errors.append({'name':e['name'],'access':e['access']});continue
 b=(Q/'primary'/(e['name']+'.pdf')).read_bytes();text=(Q/'primary'/(e['name']+'.txt')).read_bytes()
 assert len(b)==e['bytes'] and sha(b)==e['sha256'] and len(text)==e['text_bytes'] and sha(text)==e['text_sha256'];pdfs+=1
e=read(Q/'primary/Boyd-access.json');b=(Q/'primary/BoydVandenberghe2004.pdf').read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'];pdfs+=1
freeze=read(Q/'freeze-binding.json');assert freeze['sha256']==statement and freeze['bytes']==len((K/'STATEMENT.md').read_bytes())
for name,base,lo,hi,expected in [('acceptance.txt',PROJECT/'frontier/NEW-TEN-2026-10-14.md',4801,6347,'f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'),('Source344.txt',PROJECT/'sources/CONTENTS.md',578403,579066,'55b7b60b5f87b05092a145cb70843f96467b0c74e76da1c79f98159fcf3db05b')]:
 with base.open('rb') as f:f.seek(lo);b=f.read(hi-lo)
 assert sha(b)==expected and b==(Q/name).read_bytes()
for name in ['history-navigation.json','history-navigation-other.json','history-new-primitives.json']:
 e=read(Q/name);assert not e['hits']
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
 base=A/'controls';ca={'FINAL':sha((base/'packet/FINAL.md').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}
 for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode','symlink']:
  dst=Path(tmp)/case;shutil.copytree(base,dst);a=dict(ca);f=dst/'packet/sample.txt'
  if case=='wrong-anchor':a['FINAL']='0'*64
  elif case=='changed-bytes':b=f.read_bytes();f.write_bytes(bytes([b[0]^1])+b[1:])
  elif case=='extra-file':(dst/'packet/extra.txt').write_text('extra\n')
  elif case=='missing-file':f.unlink()
  elif case=='file-mode':f.chmod(0o600 if stat.S_IMODE(f.stat().st_mode)!=0o600 else 0o644)
  elif case=='directory-mode':(dst/'packet').chmod(0o700 if stat.S_IMODE((dst/'packet').stat().st_mode)!=0o700 else 0o755)
  elif case=='symlink':f.unlink();f.symlink_to('FINAL.md')
  q=run(dst,a);ok=q.returncode==0;assert ok==(case=='intact'),(case,q.stdout,q.stderr);controls.append({'case':case,'accepted':ok,'expected':case=='intact'})
assert observe(A)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'statement_sha256':statement,'proof_sha256':proof,'verifier_sha256':verifier,'verification':json.loads(v.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'packet_original_byte_bindings':len(m['files']),'canonical_blob_bindings':len(source),'logged_extent_bindings':len(logs),'primary_pdf_bindings':pdfs,'primary_access_limits':errors,'original_history_selected':0,'formal_navigation':'Exact pinned lean/docs/344.md returned HTTP404 according to read access record; no formal support claimed.','copied_controls':controls,'replay_recovery':'Initial parent duplicate-file binding assumed identical root-relative paths; packet private/code and guards copies instead map to author root basenames. Missing-path assertion was corrected in parent-only code; no artifact mismatch or original write occurred.','limits':'Parent read all authored statement, proof, derivations, comparison, FINAL, REPORT, private limits and verifier. Canonical, primary and logged extents identity-bound without inherited semantic reading. No original-history mathematical body selected by author. Accidental exposures, OCR/crop/endpoint limits and late comparison remain disclosed. Author math_sanity code read but not executed because it writes to the original root; its sample computations are not proof gates.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
 p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
