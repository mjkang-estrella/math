#!/usr/bin/env python3
"""Read-only authentication, not mathematical review."""
from pathlib import Path, PurePosixPath
import hashlib, json, stat, subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;R=D.parent/'fresh-arithmetic-discovery-r162bm'
A={'FINAL.md':'1b7719ac5b3f13b663d43917c3b417a39d035c729f923c2ec786ea0c3db10cdc','MANIFEST.json':'7b562aea83231352144c9628d01e147a58c6c2fc0c14d557c4a3b22e163d275f','REPORT.md':'bb6b47d085c26c4b968298f616a722006fd463f1df2231806a6186f1e1b5e9bd'}
def sha(a):return hashlib.sha256(a).hexdigest()
def unique(pairs):
 out={}
 for k,v in pairs:assert k not in out;out[k]=v
 return out
def read(p):return json.loads(p.read_bytes(),object_pairs_hook=unique)
def snapshot(root):
 out={}
 for p in root.rglob('*'):
  s=p.lstat();assert not stat.S_ISLNK(s.st_mode)
  if stat.S_ISREG(s.st_mode):
   a=p.read_bytes();out[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=s.st_mode)
  else:assert stat.S_ISDIR(s.st_mode)
 return out
before=read(D/'private/intake/root-before.json');assert snapshot(R)==before
for n,h in A.items():assert sha((R/n).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(R/'verify.py'),'--root',str(R),'--final-sha',A['FINAL.md'],'--manifest-sha',A['MANIFEST.json'],'--report-sha',A['REPORT.md'],'--project',str(P)],cwd=P,capture_output=True,text=True)
assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'MANIFEST.json');rows=m['files'];names=[e['path'] for e in rows]
assert names==sorted(set(names)) and len({s.casefold() for s in names})==len(names)
assert set(before)==set(names)|{'MANIFEST.json','REPORT.md'}
for e in rows:
 n=e['path'];q=PurePosixPath(n);assert not q.is_absolute() and '..' not in q.parts and q.as_posix()==n
 p=R/n;a=p.read_bytes();s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
 assert len(a)==e['bytes'] and sha(a)==e['sha256'] and s.st_mode==e['st_mode']
dns=[e['path'] for e in m['directories']];assert dns==sorted(set(dns))
assert set(dns)=={'.'}|{p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_dir()}
for e in m['directories']:assert (R/e['path']).stat().st_mode==e['st_mode']
for n,mode in m['control_modes'].items():assert (R/n).stat().st_mode==mode
a=(P/'sources/preprints-tree.json').read_bytes();assert len(a)==4858136 and sha(a)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(a);assert not tree['truncated'] and len(tree['tree'])==13223
prefix='preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026'
sel=read(R/'private/source-tree.json');expected=[e for e in tree['tree'] if e['path']==prefix or e['path'].startswith(prefix+'/')]
assert len(sel)==len(expected)==16 and {e['path']:e for e in sel}=={e['path']:e for e in expected}
blobs={e['path']:e for e in sel if e['type']=='blob'};auth=read(R/'private/source-authentication.json');assert len(auth)==len(blobs)==12
text_bytes=0;text_count=0
for e in auth:
 rel=e['path'].removeprefix('private/source/');b=blobs[prefix+'/'+rel];p=R/e['path'];a=p.read_bytes()
 assert len(a)==e['bytes']==b['size'] and sha(a)==e['sha256'] and p.stat().st_mode==e['st_mode']==int(b['mode'],8)
 assert hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['git_blob']==b['sha']
 assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+b['path']
 if not rel.endswith('.pdf'):text_count+=1;text_bytes+=len(a)
assert (text_count,text_bytes)==(11,145989)
inputs=read(R/'private/initial-inputs.json');assert len(inputs)==7
for e in inputs:
 p=P/e['original'];a=p.read_bytes();assert p.stat().st_mode==e['st_mode'] and len(a)==e['size'] and sha(a)==e['sha256'] and a==(R/e['copy']).read_bytes()
primaries=[]
for n in ['primary-fetch.json','primary-fetch2.json','primary-fetch3.json','primary-fetch4.json']:
 x=read(R/'private'/n);primaries.extend(x if isinstance(x,list) else [x])
assert len(primaries)==6
for e in primaries:
 a=(R/'private/primary'/(e['name']+'.pdf')).read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256']
statement_sha=sha((R/'STATEMENT.md').read_bytes());assert statement_sha=='6f1c7eed54c4bee7b80a56494fddfb0e5e0bcd66f0e4b9acc2a2fdb6458f5127'
ns={'__name__':'artifact_readonly','__file__':str(R/'verify.py')};exec(compile((R/'verify.py').read_bytes(),str(R/'verify.py'),'exec'),ns)
controls=[]
for i,name in enumerate(A):
 bad=list(A.values());bad[i]='0'*64
 try:ns['check'](R,*bad,project=P)
 except AssertionError as ex:assert 'anchor mismatch' in str(ex);controls.append('wrong '+name+' anchor REJECTED')
 else:raise AssertionError('Wrong anchor accepted')
tiny=R/'private/control-fixture';restored=ns['check'](tiny,*[sha((tiny/n).read_bytes()) for n in A])
assert snapshot(R)==before
out=dict(status='MATCH',scope='Artifact authentication only; no mathematical gate',bundled_verifier_passed=True,bundled_verifier_stdout=run.stdout.strip(),payload_records=len(rows),payload_bytes=sum(e['bytes'] for e in rows),whole_root_files=len(before),directories_including_root=len(dns),detached_anchors=A,statement_sha256=statement_sha,proof_sha256=sha((R/'private/PROOF.md').read_bytes()),exact_membership_hashes_lengths_full_modes_matched=True,source_tree_entries=16,source_blobs=12,canonical_text_objects=11,canonical_text_bytes=145989,primary_pdfs_independently_verified=6,initial_original_copy_pairs=7,controls=controls,restored_tiny_control=restored,whole_root_bytes_and_full_modes_unchanged=True)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
