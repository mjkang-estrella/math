#!/usr/bin/env python3
"""Read-only packet/receipt replay; controls modify only fresh parent-owned copies."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];R=C/'fresh-structural-discovery-r200';K=R/'packet';D=K/'PRIVATE'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest();mode=lambda p:format(stat.S_IMODE(p.stat().st_mode),'04o')
anchors={'FINAL':'69d42a3734a91f049f89c8f9a59d58098064f6a5f5c404d43484e2b7edf39344','MANIFEST':'83d1d733e1234a693f164bc50a677d03dc30cf2f55ffec00baf10c6000f52950','REPORT':'834eea4fd517506fc5dbf5c628fa2b0fdc5c491027d811ee2556630c42c54802'}
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
def verify(root,report,aa):
 return subprocess.run(['python3','-I','-B',str(K/'verify_packet.py'),'--root',str(root),'--manifest-sha256',aa['MANIFEST'],'--final-sha256',aa['FINAL'],'--report',str(report),'--report-sha256',aa['REPORT']],capture_output=True,text=True)
v=verify(K,R/'REPORT.md',anchors);assert v.returncode==0,(v.stdout,v.stderr)
m=read(K/'MANIFEST.json');assert len(m['files'])==58 and len(m['directories'])==17
assert all(read(R/'ANCHORS.json')[n]['sha256']==h for n,h in anchors.items())
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={x['path']:x for x in json.loads(tb)['tree']}
canonical=read(D/'canonical-auth.json');assert len(canonical)==24
for e in canonical:
 b=(D/'canonical'/e['path']).read_bytes();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();t=tree[e['path']]
 assert len(b)==e['size']==t['size'] and sha(b)==e['sha256'] and git==e['git_blob']==t['sha']
 assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
source=read(D/'source-reads.json');assert len(source)==24
for e in source:
 b=(D/'canonical'/e['path']).read_bytes();assert sha(b)==e['sha256']
 for lo,hi in e.get('read_extents',[]):assert 0<=lo<=hi<=len(b)
comparators=read(D/'comparator-auth.json');assert len(comparators)==3
for e in comparators:
 b=(D/'comparator'/e['path']).read_bytes();assert len(b)==e['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
for e in read(D/'primary/access.json'):
 b=(D/'primary'/(e['name']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
primary=read(D/'primary/read-extents.json');assert len(primary)==5
for e in primary:
 b=(D/'primary'/e['name']).read_bytes();assert sha(b)==e['sha256'];assert 0<=e['start']<e['end']<=len(b)
 # Recorded offsets use byte/LF lines; page form feeds do not create a new line.
 lines=b.splitlines(keepends=True);lo=len(b''.join(lines[:e['first_line']-1]));hi=len(b''.join(lines[:e['end_line_exclusive']-1]))
 assert (lo,hi)==(e['start'],e['end']),('primary extent mismatch',e['name'],lo,hi)
history=read(D/'history-reads.json');assert len(history)==3
for e in history:
 with (PROJECT/e['path']).open('rb') as f:f.seek(e['start']);b=f.read(e['end']-e['start'])
 assert b==(D/('I88-'+e['selection']+'.bin')).read_bytes() and sha(b)==e['selected_sha256']
for path,lo,hi,copy,h in [('sources/CONTENTS.md',549528,550877,'Source324.bin','e3562484e1e7d24d23d5412cee06304af733d6f7eb4f37d08ad67590835654a4'),('frontier/NEW-TEN-2026-10-14.md',4801,6347,'acceptance.bin','f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984')]:
 with (PROJECT/path).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
 assert b==(D/copy).read_bytes() and sha(b)==h
for name in ['AGENTS.md','upstream.json']:
 original=PROJECT/name if name=='AGENTS.md' else PROJECT/'sources'/name
 assert original.read_bytes()==(D/name).read_bytes()
controls=[]
with tempfile.TemporaryDirectory(prefix='r200-control-',dir=P) as tmp:
 T=Path(tmp);shutil.copytree(R/'controls/tiny-packet',T/'packet');shutil.copy2(R/'controls/REPORT.md',T/'REPORT.md');k=T/'packet';r=T/'REPORT.md'
 aa={'FINAL':sha((k/'FINAL.md').read_bytes()),'MANIFEST':sha((k/'MANIFEST.json').read_bytes()),'REPORT':sha(r.read_bytes())}
 def check(name,expected,override=None):
  q=verify(k,r,override or aa);ok=q.returncode==0;assert ok==expected,(name,q.stdout,q.stderr);controls.append({'case':name,'accepted':ok,'expected':expected})
 check('clean',True);payload=k/'calculation.txt';b=payload.read_bytes();m0=payload.stat().st_mode;payload.chmod(0o600);payload.write_bytes(bytes([b[0]^1])+b[1:]);payload.chmod(stat.S_IMODE(m0));check('changed-bytes',False);payload.chmod(0o600);payload.write_bytes(b);payload.chmod(stat.S_IMODE(m0));extra=k/'unselected.txt';extra.write_text('control\n');check('unselected-member',False);extra.unlink();wrong=dict(aa);wrong['FINAL']='0'*64;check('wrong-detached-anchor',False,wrong)
assert observe()==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'selected_files':len(m['files']),'selected_directories':len(m['directories']),'selected_bytes':sum(e['bytes'] for e in m['files']),'canonical_blobs':len(canonical),'source_reading_record_bindings':len(source),'comparator_bindings':len(comparators),'primary_pdf_bindings':3,'primary_reading_extents':5,'history_exact_spans':3,'instruction_catalogue_acceptance_bindings':4,'copied_controls':controls,'root_files':sum(e['type']=='file' for e in before.values()),'author_bytes_modes_unchanged':True,'limits':'Receipt binding and artifact verification are not semantic reading or mathematical grades.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');(P/'replay.json').chmod(0o600);print(json.dumps(out,indent=2))
