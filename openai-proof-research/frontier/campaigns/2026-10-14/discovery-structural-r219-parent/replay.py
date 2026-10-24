#!/usr/bin/env python3
"""Read-only artifact intake, without inherited semantic reading or grading."""
from pathlib import Path
import datetime, hashlib, json, os, shutil, stat, subprocess, tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
A=C/'fresh-structural-discovery-r219'; K=A/'packet'; Q=K/'private'
read=lambda p:json.loads(p.read_bytes())
sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'579f67bd1d23eb4099d44a615dc27e23399ead94a3e469cc4a34f15ecfcc2e08','MANIFEST':'f92926bf3cd068b7a0ec4996daff34331b38dd4cfa31dab4db4a70bb7bba8765','REPORT':'20f7b417703b24be0b3427137eed93eee56a4071b6342b49d42f227a38344257'}
def observe(root):
 out={}
 for parent,dirs,files in os.walk(root,followlinks=False):
  for p in [Path(parent),*(Path(parent)/n for n in files)]:
   assert not p.is_symlink()
   e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
   if p.is_file(): b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
   out[p.relative_to(root).as_posix()]=e
  assert all(not (Path(parent)/n).is_symlink() for n in dirs)
 return out
def run(root,a):
 return subprocess.run(['python3','-I','-B',str(A/'verify_packet.py'),'--packet',str(root/'packet'),'--manifest',str(root/'MANIFEST.json'),'--manifest-sha256',a['MANIFEST'],'--final-sha256',a['FINAL'],'--report',str(root/'REPORT.md'),'--report-sha256',a['REPORT']],capture_output=True,text=True)
before=observe(A)
assert sha((A/'verify_packet.py').read_bytes())=='cc2020677294fceb7b99bd3254cf56c93752598921aa5999853bd8ccd2892aee'
v=run(A,anchors);assert v.returncode==0,(v.stdout,v.stderr)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes()
assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']};assert len(tree)==13223
prefix='preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026'
selected=read(Q/'canonical-tree-selection.json')
assert selected==[e for e in json.loads(tb)['tree'] if e['path']==prefix or e['path'].startswith(prefix+'/')]
source=read(Q/'canonical-authentication.json');assert len(source)==14
for e in source:
 b=(Q/'canonical'/Path(e['path']).relative_to(prefix)).read_bytes();t=tree[e['path']]
 assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
formal=read(Q/'formal-navigation/authentication.json')
for e in formal:
 b=(Q/'formal-navigation'/e['path']).read_bytes()
 assert len(b)==e['bytes'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
assert (Q/'343.md').read_bytes()==(Q/'formal-navigation/lean/docs/343.md').read_bytes()
logs=[json.loads(s) for s in (Q/'reads.jsonl').read_text().splitlines()];local=history=0
for e in logs:
 lo,hi=e['byte_first'],e['byte_stop']
 if 'file' in e:
  p=K/e['file'];assert p.resolve().is_relative_to(K)
  b=p.read_bytes();lines=b.splitlines(keepends=True)
  assert lo==sum(map(len,lines[:e['line_first']-1])) and hi==sum(map(len,lines[:e['line_last']]))
  assert sha(b[lo:hi])==e['selection_sha256'];local+=1
 else:
  assert e['original'] in ['frontier/iterations/i70-symplectic-geometry-discovery.md','frontier/iterations/i74-relative-symplectic-packing.md']
  with (PROJECT/e['original']).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
  assert sha(b)==e['selected_sha256'] and b==(K/e['local_selected']).read_bytes();history+=1
assert history==4
pdfs=0;errors=[]
for e in read(Q/'primary/access.json')+read(Q/'primary/access-additional.json'):
 if 'error' in e:errors.append({'name':e['name'],'error':e['error']});continue
 b=(Q/'primary'/(e['name']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
 assert len((Q/'primary'/(e['name']+'.txt')).read_bytes())==e['text_bytes'];pdfs+=1
for name,base,lo,hi,expected in [('acceptance.txt',PROJECT/'frontier/NEW-TEN-2026-10-14.md',4801,6347,'f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'),('source343-entry.txt',PROJECT/'sources/CONTENTS.md',577254,578403,'945423078a808cba2fbf9de8decc28d8a3ba9257be93d7bd44ab6a6cc6eb8aa4')]:
 with base.open('rb') as f:f.seek(lo);b=f.read(hi-lo)
 assert sha(b)==expected and b==(Q/name).read_bytes()
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
 base=A/'copied-controls'; ca={'FINAL':sha((base/'packet/FINAL.md').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}
 for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode','symlink']:
  dst=Path(tmp)/case;shutil.copytree(base,dst);a=dict(ca);f=dst/'packet/sample.txt'
  if case=='wrong-anchor':a['FINAL']='0'*64
  elif case=='changed-bytes':b=f.read_bytes();f.write_bytes(bytes([b[0]^1])+b[1:])
  elif case=='extra-file':(dst/'packet/extra.txt').write_text('extra\n')
  elif case=='missing-file':f.unlink()
  elif case=='file-mode':f.chmod(0o644)
  elif case=='directory-mode':(dst/'packet').chmod(0o755)
  elif case=='symlink':f.unlink();f.symlink_to('FINAL.md')
  q=run(dst,a);ok=q.returncode==0;assert ok==(case=='intact'),(case,q.stdout,q.stderr)
  controls.append({'case':case,'accepted':ok,'expected':case=='intact'})
assert observe(A)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'source_canonical_blobs':len(source),'formal_identity_bindings':len(formal),'logged_local_extent_bindings':local,'exact_original_history_span_bindings':history,'primary_pdf_bindings':pdfs,'primary_access_errors':errors,'copied_controls':controls,'limits':'Parent semantically read complete DERIVATIONS, READING-LIMITS, FINAL, REPORT and verifier. Underlying canonical, primary, formal and original-history bodies identity-bound only, without inherited semantic reading. Author timing, primary intermediates, OCR/crop limits and accidental exposures remain disclosed; no exhaustive history clearance, mathematical grade or completed formal support.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
 p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
