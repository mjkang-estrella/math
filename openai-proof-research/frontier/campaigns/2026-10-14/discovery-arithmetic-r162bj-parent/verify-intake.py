#!/usr/bin/env python3
"""Read-only artifact authentication, with the initial permission-only limit preserved."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;R=D.parent/'fresh-arithmetic-discovery-r162bj'
A={'FINAL.md':'259a81d279b9d5389763e59f6849d3d81536b7ac8a6369c7902cb1a45ea32729','MANIFEST.json':'78d645f3a2f0772faa32bdb2da46766183067148b9fd05bb27beecbff52e73f7','REPORT.md':'5542daa88a0e6f8a4109d251241d519504a5e9c31a3e41276c71d242e8b0a89a'}
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
for n,h in A.items():assert sha((R/n).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(R/'private/verify_packet.py'),'--root',str(R),'--project',str(P),'--final-hash',A['FINAL.md'],'--manifest-hash',A['MANIFEST.json'],'--report-hash',A['REPORT.md'],'--manifest-bytes','18145','--report-bytes','1590','--manifest-mode','33188','--report-mode','33188'],cwd=P,capture_output=True,text=True)
assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'MANIFEST.json');rows=m['files'];names=[e['path'] for e in rows]
assert names==sorted(set(names)) and len({s.casefold() for s in names})==len(names)
assert set(before)==set(names)|{'MANIFEST.json','REPORT.md'} and 'FINAL.md' in names
for e in rows:
 n=e['path'];q=PurePosixPath(n);assert not q.is_absolute() and '..' not in q.parts and q.as_posix()==n
 p=R/n;a=p.read_bytes();st=p.lstat();assert stat.S_ISREG(st.st_mode) and st.st_nlink==1
 assert len(a)==e['bytes'] and sha(a)==e['sha256'] and st.st_mode==e['full_mode']
dns=[e['path'] for e in m['directories']];assert dns==sorted(set(dns))
assert set(dns)=={'.'}|{p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_dir()}
for e in m['directories']:assert (R/e['path']).stat().st_mode==e['full_mode']
selected=read(R/'private/selected-tree.json');a=(P/'sources/preprints-tree.json').read_bytes();assert len(a)==4858136 and sha(a)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(a);assert not tree['truncated'];folders=[e['path'] for e in selected if e['type']=='tree' and e['path'].count('/')==1]
assert len(folders)==2 and selected==[e for e in tree['tree'] if any(e['path']==z or e['path'].startswith(z+'/') for z in folders)]
blobs={e['path']:e for e in selected if e['type']=='blob'};auth=read(R/'private/source-bindings.json');assert {e['path'] for e in auth}==set(blobs) and len(auth)==34
text_bytes=0
for e in auth:
 b=blobs[e['path']];assert e['local']=='private/source/'+e['path'];p=R/e['local'];a=p.read_bytes()
 assert len(a)==e['bytes']==b['size'] and sha(a)==e['sha256'] and p.stat().st_mode==int(e['git_mode'],8)==int(b['mode'],8)
 assert hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['git_blob']==b['sha']
 assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 if not e['path'].endswith('.pdf'):text_bytes+=len(a)
assert text_bytes==493280 and len(selected)==45
initial=read(D/'private/completed-direct-inputs.json');copies=read(R/'private/completed-context-bindings.json');assert len(initial)==len(copies)==5
for e,c in zip(initial,copies):
 assert e['path']==c['original'] and e['bytes']==c['bytes'] and e['sha256']==c['sha256'] and stat.S_IMODE(e['mode'])==c['mode']
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode'] and a==(R/c['copy']).read_bytes()
primary=[e for e in read(R/'private/primary/bindings.json') if 'bytes' in e];assert len(primary)==3
for e in primary:
 a=(R/'private/primary'/(e['name']+'.pdf')).read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256']
 assert (R/'private/primary'/(e['name']+'.txt')).stat().st_size==e['text_bytes']
ns={'__name__':'artifact_readonly','__file__':str(R/'private/verify_packet.py')};exec(compile((R/'private/verify_packet.py').read_bytes(),str(R/'private/verify_packet.py'),'exec'),ns)
args=list(A.values());results=[]
for i in range(3):
 bad=args.copy();bad[i]='0'*64
 try:ns['verify'](R,P,*bad,18145,1590,33188,33188)
 except AssertionError as ex:assert 'anchor' in str(ex);results.append('wrong '+list(A)[i]+' anchor REJECTED')
 else:raise AssertionError('Wrong anchor accepted')
f=R/'private/controls/tiny';fa=[sha((f/n).read_bytes()) for n in A];ns['verify'](f,P,*fa,(f/'MANIFEST.json').stat().st_size,(f/'REPORT.md').stat().st_size,33188,33188);results.append('existing restored tiny fixture MATCH')
assert snapshot(R)==before
out=dict(status='MATCH',scope='Artifact authentication only; no mathematical gate',bundled_verifier_passed=True,bundled_verifier_stdout=run.stdout.strip(),payload_records=len(rows),payload_bytes=sum(e['bytes'] for e in rows),whole_root_files=len(before),directories_including_root=len(dns),detached_anchors=A,duplicate_keys_rejected=True,exact_membership_hashes_lengths_full_modes_matched=True,source_tree_entries=45,source_blobs=34,source_texts=32,source_text_bytes=text_bytes,primary_pdfs_independently_verified=3,initial_completed_original_and_copy_pairs=5,author_initial_context_full_modes_recorded=False,author_initial_context_permission_bits_matched=True,parent_predispatch_ledger_original_full_modes_matched=True,mode_record_limitation_preserved=True,controls=results,whole_root_bytes_and_full_modes_unchanged=True)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
