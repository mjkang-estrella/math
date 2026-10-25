#!/usr/bin/env python3
"""Read-only artifact authentication. This assigns no mathematical gate."""
from pathlib import Path, PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;R=D.parent/'fresh-arithmetic-discovery-r162bf'
ANCHORS=dict(zip(['FINAL.md','MANIFEST.json','REPORT.md'],['bdf76ac1d36d173c96235e275c94b5032d731b6734ef8cfd9e61cf80ef61626c','0500da1df32aef4a31df8fb1f38c74220e68ae367e0d1dfee8a17ed41453adbb','57985cfff6604cd55b2027198c4f023997c23ca97c99945f15c576dd8b7913bd']))
def sha(a):return hashlib.sha256(a).hexdigest()
def unique(pairs):
 out={}
 for k,v in pairs:assert k not in out;out[k]=v
 return out
def read(p):return json.loads(p.read_bytes(),object_pairs_hook=unique)
def snapshot(root):
 out={}
 for p in root.rglob('*'):
  st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
  if stat.S_ISREG(st.st_mode):
   a=p.read_bytes();out[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=st.st_mode)
  else:assert stat.S_ISDIR(st.st_mode)
 return out
before=read(D/'private/intake/root-before.json');assert snapshot(R)==before
for n,h in ANCHORS.items():assert sha((R/n).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(R/'VERIFY.py'),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']],cwd=P,capture_output=True,text=True)
assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'MANIFEST.json');rows=m['files'];names=[e['path'] for e in rows]
assert names==sorted(set(names)) and len({s.casefold() for s in names})==len(names)
for e in rows:
 n=e['path'];q=PurePosixPath(n);assert not q.is_absolute() and '..' not in q.parts and q.as_posix()==n
 p=R/n;a=p.read_bytes();st=p.lstat();assert stat.S_ISREG(st.st_mode) and st.st_nlink==1
 assert len(a)==e['bytes'] and sha(a)==e['sha256'] and st.st_mode==e['mode']
assert set(before)==set(names)|{'MANIFEST.json','REPORT.md'} and 'FINAL.md' in names
selected=read(R/'private/source/selected-tree.json');whole=Path(P/'sources/preprints-tree.json').read_bytes()
assert len(whole)==4858136 and sha(whole)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(whole);assert not tree['truncated'];folders=[e['path'] for e in selected if e['type']=='tree' and e['path'].count('/')==1]
assert len(folders)==2 and selected==[e for e in tree['tree'] if any(e['path']==z or e['path'].startswith(z+'/') for z in folders)]
blobs={e['path']:e for e in selected if e['type']=='blob'};auth=read(R/'private/source/authentication.json');assert {e['path'] for e in auth}==set(blobs) and len(auth)==24
text_bytes=0
for e in auth:
 b=blobs[e['path']];p=R/'private/source'/e['path'];a=p.read_bytes()
 assert len(a)==e['bytes']==b['size'] and sha(a)==e['sha256'] and p.stat().st_mode==int(e['mode'],8)==int(b['mode'],8)
 assert hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['git_blob']==b['sha']
 assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 if not e['path'].endswith('.pdf'):text_bytes+=len(a)
assert text_bytes==244917 and len(selected)==29
initial=read(D/'private/completed-direct-inputs.json');copies=read(R/'private/context/copies.json');assert len(initial)==len(copies)==5
for e,c in zip(initial,copies):
 assert e['path']==c['original'] and e['bytes']==c['bytes'] and e['sha256']==c['sha256'] and e['mode']==int(c['mode'],8)
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode'] and a==(R/c['copy']).read_bytes()
ns={'__name__':'artifact_readonly','__file__':str(R/'VERIFY.py')};exec(compile((R/'VERIFY.py').read_bytes(),str(R/'VERIFY.py'),'exec'),ns)
args=[ANCHORS[n] for n in ['FINAL.md','MANIFEST.json','REPORT.md']];controls=[]
for i in range(3):
 bad=args.copy();bad[i]='0'*64
 try:ns['verify_envelope'](R,*bad)
 except AssertionError as ex:
  assert 'anchor mismatch' in str(ex);controls.append('wrong '+list(ANCHORS)[i]+' anchor REJECTED')
 else:raise AssertionError('Wrong detached anchor accepted')
fixture=R/'private/envelope-control';fa=[sha((fixture/n).read_bytes()) for n in ANCHORS]
ns['verify_envelope'](fixture,*fa);controls.append('existing restored tiny fixture MATCH')
assert snapshot(R)==before
out=dict(status='MATCH',scope='Artifact authentication only; no mathematical gate',bundled_verifier_passed=True,bundled_verifier_stdout=run.stdout.strip(),payload_records=len(rows),payload_bytes=sum(e['bytes'] for e in rows),whole_root_files=len(before),directories_including_root=1+sum(p.is_dir() for p in R.rglob('*')),detached_anchors=ANCHORS,duplicate_keys_rejected=True,exact_membership_hashes_lengths_full_modes_matched=True,source_tree_entries=29,source_blobs=24,source_texts=22,source_text_bytes=text_bytes,initial_completed_original_and_copy_pairs=5,initial_original_full_modes_unchanged=True,controls=controls,whole_root_bytes_and_full_modes_unchanged=True)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
