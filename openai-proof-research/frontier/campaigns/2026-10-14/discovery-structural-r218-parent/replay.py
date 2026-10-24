#!/usr/bin/env python3
"""Read-only author-packet replay and proportionate parent-owned tiny controls."""
from pathlib import Path
import datetime, hashlib, json, os, stat, subprocess, sys, tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]; A=C/'fresh-structural-discovery-r218'
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL':'ca7a9383a8a5e1c76b26878c5d4bb37df778a37829aed28f9a6d180264ea2d6d','MANIFEST':'43459b97cf417a8ad9356615ec82ff34b1be390d9af635cc2e331e3be340f058','REPORT':'c4cd44df76a48a268d82c1c4b8d16be62dd6dacf32713f7bdbe5793a927f9a7f'}
def snapshot():
 out={'files':{},'directories':{}}
 for base,ds,fs in os.walk(A,followlinks=False):
  b=Path(base); out['directories'][b.relative_to(A).as_posix()]=oct(stat.S_IMODE(b.stat().st_mode))
  for n in ds+fs: assert not (b/n).is_symlink()
  for n in fs:
   f=b/n; out['files'][f.relative_to(A).as_posix()]={'bytes':f.stat().st_size,'sha256':sha(f.read_bytes()),'mode':oct(stat.S_IMODE(f.stat().st_mode))}
 return out
before=snapshot(); verifier=A/'verify_packet.py'
assert sha(verifier.read_bytes())=='cbebecb8a0bd40d6e71966a2d575240a7a3036d58b1fd3167d0e4265b58bd939'
def run(root,an):
 return subprocess.run([sys.executable,'-I','-B',str(verifier),'--root',str(root),'--final-sha',an['FINAL'],'--manifest-sha',an['MANIFEST'],'--report-sha',an['REPORT']],capture_output=True,text=True)
result=run(A,anchors); assert result.returncode==0,result.stderr
m=read(A/'MANIFEST.json'); assert len(m['files'])==85 and len(m['directories'])==16
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={x['path']:x for x in json.loads(tb)['tree']}
for meta in ['canonical-authentication.json','companion-authentication.json','lean-authentication.json']:
 for x in read(A/'private'/meta):
  b=(A/'private/canonical'/x['path']).read_bytes(); h=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert len(b)==x['bytes'] and sha(b)==x['sha256'] and h==x['git_blob']
  if x['path'].startswith('preprints/'): assert tree[x['path']]['sha']==h and tree[x['path']]['size']==len(b)
base=A/'private/canonical/preprints'; octo=base/'Taming-implies-compatibility-on-four-manifolds-October-6-2026'; sept=base/'Taming-implies-compatibility-on-four-manifolds-September-23-2026'
eq=read(A/'private/version-equality.json')
for x in eq: assert ((octo/x['path']).read_bytes()==(sept/x['path']).read_bytes())==x['byte_equal']
primary=[]
for name in ['access.json','access-2.json']:
 for x in read(A/'private/primary'/name):
  b=(A/'private/primary'/(x['id']+'.pdf')).read_bytes(); assert len(b)==x['bytes'] and sha(b)==x['sha256']
  assert (A/'private/primary'/(x['id']+'.txt')).stat().st_size==x['text_bytes']; primary.append(x['id'])
extents=[]
for name in ['semantic-selections-1.json','semantic-selections-2.json','semantic-selections-3.json','semantic-selections-4.json','semantic-selections-5.json']:
 for x in read(A/'private'/name):
  b=(A/x['path']).read_bytes(); lo=x['start']; hi=x['end']; assert 0<=lo<hi<=len(b)
  extents.append({'path':x['path'],'bytes':[lo,hi],'sha256':sha(b[lo:hi])})
for name,lo,hi,_ in read(A/'private/semantic-selections-DLZ.json'):
 assert any(x['path']=='private/primary/'+name+'.txt' and x['bytes']==[lo,hi] for x in extents)
freeze=read(A/'private/freeze-anchor.json'); assert sha((A/freeze['path']).read_bytes())==freeze['sha256'] and (A/freeze['path']).stat().st_size==freeze['bytes'] and stat.S_IMODE((A/freeze['path']).stat().st_mode)==int(freeze['mode'],8)
proof=sha((A/'AUTHOR-PROOF.md').read_bytes()); assert proof=='cbfb43a1bf679f28ad840e418009ff4198428d8ba84bd7f22cbb638d40e1619f'
checks=subprocess.run([sys.executable,'-I','-B',str(A/'algebra_checks.py')],capture_output=True,text=True); assert checks.returncode==0,checks.stderr
controls=[]
for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
 with tempfile.TemporaryDirectory(prefix='tiny-r218-',dir=P) as td:
  root=Path(td); (root/'d').mkdir(mode=0o700); (root/'FINAL.md').write_bytes(b'tiny final\n'); (root/'d/item.txt').write_bytes(b'payload\n'); (root/'REPORT.md').write_bytes(b'tiny outside report\n')
  for f in [root/'FINAL.md',root/'d/item.txt',root/'REPORT.md']: f.chmod(0o400)
  mm={'files':{n:{'bytes':(root/n).stat().st_size,'sha256':sha((root/n).read_bytes()),'mode':'0400'} for n in ['FINAL.md','d/item.txt']},'directories':{'d':'0700'}}
  (root/'MANIFEST.json').write_text(json.dumps(mm)); an={k:sha((root/(k+'.md' if k!='MANIFEST' else 'MANIFEST.json')).read_bytes()) for k in anchors}
  if case=='wrong-anchor': an['FINAL']='0'*64
  elif case=='changed-bytes': (root/'d/item.txt').chmod(0o600); (root/'d/item.txt').write_bytes(b'changed\n'); (root/'d/item.txt').chmod(0o400)
  elif case=='extra-file': (root/'extra.txt').write_bytes(b'x')
  elif case=='missing-file': (root/'d/item.txt').unlink()
  elif case=='file-mode': (root/'d/item.txt').chmod(0o600)
  elif case=='directory-mode': (root/'d').chmod(0o750)
  accepted=run(root,an).returncode==0; assert accepted==(case=='intact'); controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
after=snapshot(); assert after==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verifier_sha256':sha(verifier.read_bytes()),'statement_sha256':freeze['sha256'],'proof_sha256':proof,'verification':{'files':len(m['files']),'directories_excluding_root':len(m['directories']),'stdout':result.stdout.strip()},'root_files':len(before['files']),'root_directories_including_root':len(before['directories']),'originals_bytes_modes_unchanged':True,'source_canonical_blobs':25,'companion_blobs':3,'lean_blob_identity_bindings':2,'cross_version_byte_equalities':sum(x['byte_equal'] for x in eq),'primary_pdf_bindings':len(primary),'primary_extent_bindings':len(extents),'original_history_mathematical_bodies_admitted':0,'algebra_check':checks.stdout.strip(),'copied_controls':controls,'formal_navigation':'Author reports authenticated exact linked comparator endpoint by sorry; identity-bound locally, no formal support or compilation claimed.','limits':'Parent semantically read full frozen theorem, author proof, derivations, comparison, final, report, reading limits, validation, algebra code and verifier. Source/primary/comparator bodies identity-bound only; no inherited semantic reading, exhaustive history clearance or mathematical grade. Primary extents include disclosed editorial exposure and do not certify clean or exhaustive semantic coverage.'}
for name,obj in [('replay.json',out),('observed-root.json',before),('extent-bindings.json',extents)]:
 f=P/name; f.write_text(json.dumps(obj,indent=2)+'\n'); f.chmod(0o600)
print(json.dumps(out,indent=2))
