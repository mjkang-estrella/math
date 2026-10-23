#!/usr/bin/env python3
"""Read-only author packet/receipt checks; copy tiny controls into parent scratch."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];R=C/'fresh-structural-discovery-r202';D=R/'private'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest();mode=lambda p:format(stat.S_IMODE(p.stat().st_mode),'04o')
anchors={'FINAL':'a93c007024bad1b9dbd95b8a7df0afe91507e2cf4f37d7fad3f16a79b0a9d2b3','MANIFEST':'d6801b380b558eb16b7bb1c668d3490c58fdcdccea14869cd05461ef5d0aa5b7','REPORT':'59217c7b44cabdaac07e78ca354ad11670f52456bbb4a4e0ce400dd0b4ea133c'}
def observe():
 out={'.':{'mode':mode(R),'type':'directory'}}
 for p in sorted(R.rglob('*')):
  assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':mode(p)}
  if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
  out[p.relative_to(R).as_posix()]=e
 return out
before=observe();baseline=P/'observed-root.json'
if baseline.exists():assert read(baseline)==before
else:baseline.write_text(json.dumps(before,indent=2)+'\n');baseline.chmod(0o600)
def verify(k,a):
 return subprocess.run(['python3','-I','-B',str(R/'verify_packet.py'),'--root',str(k),'--manifest-sha256',a['MANIFEST'],'--final-sha256',a['FINAL'],'--report-sha256',a['REPORT']],capture_output=True,text=True)
v=verify(R,anchors);assert v.returncode==0,(v.stdout,v.stderr)
m=read(R/'MANIFEST.json');assert len(m['entries'])==119
f=read(R/'FINAL.json');fr=read(D/'freeze-record.json');assert f['frozen_sha256']==fr['sha256']==sha((R/'FROZEN-STATEMENT.md').read_bytes())=='fbd2600bdc050aac6e4ab130c3d4a35f88db4fa2af26b5e2b163ee922d760433'
assert fr['bytes']==(R/'FROZEN-STATEMENT.md').stat().st_size==2443 and fr['mode']==mode(R/'FROZEN-STATEMENT.md')=='0444'
assert f['selected_file_count']==119 and f['selected_bytes']==sum(e['bytes'] for e in m['entries'])==34388992
assert sha((R/'AUTHOR-PROOF.md').read_bytes())=='121ae56cd4b1444ed373549589c3f53a68fc22e9556c2f959a34084bbcc86b80'
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={e['path']:e for e in json.loads(tb)['tree']}
canonical=read(D/'canonical-auth.json');assert len(canonical)==10
for e in canonical:
 b=(R/e['local']).read_bytes();t=tree[e['path']];assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
 assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
source=read(D/'read-extents.json');assert len(source)==11
for e in source:b=(R/e['path']).read_bytes();assert e['bytes']==[0,len(b)]
for auth,body in [('Cotype-auth.json','Cotype.lean'),('lean326-auth.json','lean326.md')]:
 e=read(D/auth);b=(D/body).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
primary=read(D/'primary-access.json');assert len(primary)==6
for e in primary:b=(D/'primary'/(e['key']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
for auth,body in [('Figiel73-access.json','Figiel73.pdf'),('JM88-pdf-auth.json','JM88.pdf')]:
 e=read(D/'primary'/auth);b=(D/'primary'/body).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
history=read(D/'history-read-extents.json');assert len(history)==3
for e in history:
 lo,hi=e['bytes_half_open']
 with (PROJECT/e['original_path']).open('rb') as f0:f0.seek(lo);b=f0.read(hi-lo)
 assert b==(R/e['local']).read_bytes()
for path,lo,hi,copy,h in [('sources/CONTENTS.md',552844,553766,'source326-catalogue-range.txt','21245be0da9bcf095bab3fd68057f9d6219a848462f16dd14068824f941e178c'),('frontier/NEW-TEN-2026-10-14.md',4801,6347,'acceptance-range.txt','f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984')]:
 with (PROJECT/path).open('rb') as f0:f0.seek(lo);b=f0.read(hi-lo)
 assert b==(D/copy).read_bytes() and sha(b)==h
assert (PROJECT/'AGENTS.md').read_bytes()==(D/'AGENTS.md').read_bytes();assert (PROJECT/'sources/upstream.json').read_bytes()==(D/'upstream.json').read_bytes()
controls=[]
with tempfile.TemporaryDirectory(prefix='r202-controls-',dir=P) as tmp:
 for name,wanted in [('good',True),('changed-bytes',False),('changed-mode',False)]:
  dst=Path(tmp)/name;shutil.copytree(R/'controls'/name,dst);a={line.split()[0].split('.')[0]:line.split()[1] for line in (dst/'ANCHORS.txt').read_text().splitlines()};q=verify(dst,a);ok=q.returncode==0;assert ok==wanted,(name,q.stdout,q.stderr);controls.append({'case':name,'accepted':ok,'expected':wanted})
assert observe()==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'selected_files':119,'selected_bytes':34388992,'canonical_blobs':10,'source_and_comparator_reading_bindings':11,'formal_file_bindings':2,'primary_pdf_bindings':8,'selected_render_files':sum(e['path'].startswith('private/primary/renders/') for e in m['entries']),'history_exact_spans':3,'catalogue_acceptance_instruction_bindings':4,'copied_controls':controls,'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'author_bytes_modes_unchanged':True,'frozen_statement_sha256':fr['sha256'],'author_proof_sha256':sha((R/'AUTHOR-PROOF.md').read_bytes()),'limits':'Author verifier binds exact selected FILES and their modes, plus detached anchor contents. It does not manifest directory modes or outside-file modes. Parent separately baselines and preserves all observed directory/file modes; no author reseal. Receipt/render authentication is not semantic reading; some primary artifacts are explicitly unread.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');(P/'replay.json').chmod(0o600);print(json.dumps(out,indent=2))
