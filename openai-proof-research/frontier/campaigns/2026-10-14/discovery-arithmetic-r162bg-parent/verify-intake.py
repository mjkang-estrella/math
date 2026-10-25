#!/usr/bin/env python3
"""Read-only artifact authentication; no mathematical verdict."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;R=D.parent/'fresh-arithmetic-discovery-r162bg'
ANCHORS={'FINAL.md':'1d3f7367820e6b47ca0e25e0af91c57c2fd692757f5c5b97e1300189bd456882','private/MANIFEST.json':'8360a137751cbbf81790cc9b860483ca618d937aa126ba6d63c9730d4fe58ee5','REPORT.md':'3dd9d8e2c2dff8a667163510b6faa80b8d5c69ec4936775d7b4b5719d563bf6e'}
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
run=subprocess.run(['python','-I','-B',str(R/'private/verify_packet.py'),'--root',str(R),'--final-sha',ANCHORS['FINAL.md'],'--manifest-sha',ANCHORS['private/MANIFEST.json'],'--report-sha',ANCHORS['REPORT.md']],cwd=P,capture_output=True,text=True)
assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'private/MANIFEST.json');rows=m['files'];names=[e['path'] for e in rows];controls={'private/MANIFEST.json','REPORT.md','ANCHORS.json'}
assert names==sorted(set(names)) and len({s.casefold() for s in names})==len(names)
assert set(before)==set(names)|controls and 'FINAL.md' in names
for e in rows:
 n=e['path'];q=PurePosixPath(n);assert not q.is_absolute() and '..' not in q.parts and q.as_posix()==n
 p=R/n;a=p.read_bytes();st=p.lstat();assert stat.S_ISREG(st.st_mode) and st.st_nlink==1
 assert len(a)==e['bytes'] and sha(a)==e['sha256'] and st.st_mode==e['mode']
dns=[x['path'] for x in m['directories']];assert dns==sorted(set(dns))
assert set(dns)=={'.'}|{p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_dir()}
for e in m['directories']:assert (R/e['path']).stat().st_mode==e['mode']
selected=read(R/'private/source-tree.json');a=(P/'sources/preprints-tree.json').read_bytes();assert len(a)==4858136 and sha(a)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(a);assert not tree['truncated'];folders=[e['path'] for e in selected if e['type']=='tree' and e['path'].count('/')==1]
assert len(folders)==1 and selected==[e for e in tree['tree'] if any(e['path']==z or e['path'].startswith(z+'/') for z in folders)]
blobs={e['path']:e for e in selected if e['type']=='blob'};auth=read(R/'private/source-bindings.json');assert {e['path'] for e in auth}==set(blobs) and len(auth)==15
text_bytes=0
for e in auth:
 b=blobs[e['path']];p=P/e['local'];assert p.is_relative_to(R/'private/source');a=p.read_bytes()
 assert len(a)==e['bytes']==b['size'] and sha(a)==e['sha256'] and p.stat().st_mode==int(b['mode'],8)
 assert hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['git_blob']==b['sha']
 assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 if not e['path'].endswith('.pdf'):text_bytes+=len(a)
assert text_bytes==198440 and len(selected)==19
initial=read(D/'private/completed-direct-inputs.json');copies=read(R/'private/completed-bindings.json');assert len(initial)==len(copies)==5
for e,c in zip(initial,copies):
 assert e['path']==c['original'] and e['bytes']==c['bytes'] and e['sha256']==c['sha256'] and e['mode']==c['mode']
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode'] and a==(R/c['copy']).read_bytes()
ns={'__name__':'artifact_readonly','__file__':str(R/'private/verify_packet.py')};exec(compile((R/'private/verify_packet.py').read_bytes(),str(R/'private/verify_packet.py'),'exec'),ns)
args=list(ANCHORS.values());results=[]
for i in range(3):
 bad=args.copy();bad[i]='0'*64
 try:ns['verify'](R,*bad)
 except ValueError as ex:assert 'detached' in str(ex) and 'anchor' in str(ex);results.append('wrong '+list(ANCHORS)[i]+' anchor REJECTED')
 else:raise AssertionError('Wrong detached anchor accepted')
fixture=R/'private/controls/tiny';fa=read(fixture/'ANCHORS.json');ns['verify'](fixture,fa['FINAL.md'],fa['private/MANIFEST.json'],fa['REPORT.md']);results.append('existing restored tiny fixture MATCH')
assert snapshot(R)==before
out=dict(status='MATCH',scope='Artifact authentication only; no mathematical gate',bundled_verifier_passed=True,bundled_verifier_stdout=run.stdout.strip(),payload_records=len(rows),payload_bytes=sum(e['bytes'] for e in rows),whole_root_files=len(before),directories_including_root=len(dns),detached_anchors=ANCHORS,duplicate_keys_rejected=True,exact_membership_hashes_lengths_full_modes_matched=True,source_tree_entries=19,source_blobs=15,source_texts=14,source_text_bytes=text_bytes,initial_completed_original_and_copy_pairs=5,initial_original_full_modes_unchanged=True,controls=results,whole_root_bytes_and_full_modes_unchanged=True)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
