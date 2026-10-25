#!/usr/bin/env python3
"""Read-only artifact validation of R162BO, not a mathematical gate."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;R=D.parent/'fresh-arithmetic-discovery-r162bo'
A={'FINAL.md':'b2027b4695e720f4528db7ed078c1bc512deeae1aab7ff96dc903d56e49250c7','MANIFEST.json':'39c148e77c5b7f7dd834c3eee1d5f7e945459d1e8e14269b2159c3df59f61dd6','REPORT.md':'e2fe7fbea2bdb6605f5357a6be582b5ca901067ff879347d6c30c6c661e55a73'}
def sha(a):return hashlib.sha256(a).hexdigest()
def unique(xs):
 d={}
 for k,v in xs:assert k not in d;d[k]=v
 return d
def read(p):return json.loads(p.read_bytes(),object_pairs_hook=unique)
def snap(root):
 out={}
 for p in root.rglob('*'):
  s=p.lstat();assert not stat.S_ISLNK(s.st_mode)
  if stat.S_ISREG(s.st_mode):a=p.read_bytes();out[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=s.st_mode)
  else:assert stat.S_ISDIR(s.st_mode)
 return out
before=read(D/'private/intake/root-before.json');assert snap(R)==before
for n,h in A.items():assert sha((R/n).read_bytes())==h
vp=R/'private/verify_packet.py'
run=subprocess.run(['python','-I','-B',str(vp),'--root',str(R),'--project',str(P),'--final-sha',A['FINAL.md'],'--manifest-sha',A['MANIFEST.json'],'--report-sha',A['REPORT.md']],cwd=P,capture_output=True,text=True)
assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'MANIFEST.json');names=[e['path'] for e in m['files']];assert names==sorted(set(names)) and len({n.casefold() for n in names})==len(names)
assert set(before)==set(names)|{'MANIFEST.json','REPORT.md'}
for e in m['files']:
 q=PurePosixPath(e['path']);assert not q.is_absolute() and '..' not in q.parts and str(q)==e['path']
 p=R/e['path'];a=p.read_bytes();s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1 and len(a)==e['bytes'] and sha(a)==e['sha256'] and s.st_mode==e['mode']
dns=[e['path'] for e in m['directories']];assert dns==sorted(set(dns)) and set(dns)=={'.'}|{p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_dir()}
for e in m['directories']:assert (R/e['path']).stat().st_mode==e['mode']
raw=(P/'sources/preprints-tree.json').read_bytes();assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(raw);assert len(tree['tree'])==13223 and not tree['truncated'];family='preprints/The-entropy-rate-dimension-formula-for-self-similar-measures-on-the-line-September-24-2026'
expected=[e for e in tree['tree'] if e['path']==family or e['path'].startswith(family+'/')];sel=read(R/'private/canonical-tree.json');assert len(sel)==len(expected)==13 and {e['path']:e for e in sel}=={e['path']:e for e in expected}
ledger=read(D/'private/completed-direct-inputs.json');copies=read(R/'private/completed-bindings.json');by={e['original']:e for e in copies};assert len(ledger)==len(copies)==5
for e in ledger:
 c=by[e['path']];p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes']==c['bytes'] and sha(a)==e['sha256']==c['sha256'] and p.stat().st_mode==e['mode']==c['mode'] and a==(R/c['copy']).read_bytes()
freeze=read(R/'private/FREEZE.json');assert sha((R/'STATEMENT.md').read_bytes())==freeze['statement_sha256']=='9cb4d1e0d622b3419b852a6926ac126bb071969c9808ba35e864752af5d8c4ed'
assert sha((R/'PROOF.md').read_bytes())=='30436baec6c0bc75a07b22ed13474540861093bdcd0f22a2b985661bf1c982c7'
ns={'__name__':'artifact','__file__':str(vp)};exec(compile(vp.read_bytes(),str(vp),'exec'),ns);controls=[]
for n in A:
 b=dict(A);b[n]='0'*64
 try:ns['verify'](R,b['FINAL.md'],b['MANIFEST.json'],b['REPORT.md'],project=P)
 except ValueError as ex:assert 'anchor mismatch' in str(ex);controls.append(n+' wrong anchor rejected')
 else:raise AssertionError('wrong anchor accepted')
tiny=R/'private/controls';th={n:sha((tiny/n).read_bytes()) for n in A};restored=ns['verify'](tiny,th['FINAL.md'],th['MANIFEST.json'],th['REPORT.md'],bindings=False)
assert snap(R)==before
out=dict(status='MATCH',mathematical_grade=False,bundled_verifier=run.stdout.strip(),payload_files=len(names),payload_bytes=sum(e['bytes'] for e in m['files']),whole_files=len(before),directories=len(dns),source_entries=13,source_blobs=10,primary_pdfs=7,pinned_supplement_pdfs=3,original_copy_pairs=5,all_bytes_and_full_modes_unchanged=True,anchors=A,statement_sha256=freeze['statement_sha256'],proof_sha256=sha((R/'PROOF.md').read_bytes()),controls=controls,restored_tiny_fixture=restored)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
