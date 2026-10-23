#!/usr/bin/env python3
"""Read-only Structural201 packet/receipt comparison; copied controls only."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];R=C/'fresh-structural-discovery-r201';K=R/'packet';D=K/'private'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest();mode=lambda p:format(stat.S_IMODE(p.stat().st_mode),'04o')
anchors={'FINAL':'c5011c7cc147672a9431324be28ae439997ba866a61b69e8b6b5e3ac5d6a3543','MANIFEST':'ad691c7f3b0e11aa5e96ab91079c76043924d0faacd22b7d92177a0ac15b9270','REPORT':'6df49ae7ca1c5f98b0b0009053a40f99a14f21fd5db7d2e5fed84bed7ae1ff79'}
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
def verify(k,r,aa):
 assert k.resolve() not in r.resolve().parents
 return subprocess.run(['python3','-I','-B',str(K/'verify_packet.py'),'--packet',str(k),'--manifest-sha256',aa['MANIFEST'],'--final-sha256',aa['FINAL'],'--report',str(r),'--report-sha256',aa['REPORT']],capture_output=True,text=True)
v=verify(K,R/'REPORT.md',anchors);assert v.returncode==0,(v.stdout,v.stderr)
m=read(K/'MANIFEST.json');assert len(m['files'])==54 and len(m['directories'])==12
assert all(read(R/'ANCHORS.json')[n]['sha256']==h for n,h in anchors.items())
assert sha((R/'controls/results.json').read_bytes())==read(R/'ANCHORS.json')['controls_results_sha256']
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={e['path']:e for e in json.loads(tb)['tree']}
canonical=read(D/'canonical-authentication.json');assert len(canonical)==10
for e in canonical:
 b=(D/e['local']).read_bytes();t=tree[e['path']];assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
 assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
s=read(D/'semantic-reading.json');assert len(s['canonical_semantic_reads'])==8
for e in s['canonical_semantic_reads']:
 b=(D/'canonical'/e['file']).read_bytes();assert e['bytes']==[0,len(b)]
 if 'display_batches' in e:assert e['display_batches'][0][0]==0 and e['display_batches'][-1][1]==len(b) and all(x[1]==y[0] for x,y in zip(e['display_batches'],e['display_batches'][1:]))
comparators=read(D/'comparator-authentication.json');assert len(comparators)==5
for e in comparators:
 b=(D/'comparator'/Path(e['path']).name).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
e=read(D/'lean-325-authentication.json');b=(D/'lean-325.md').read_bytes();assert len(b)==e['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']
acquired=[e for e in read(D/'primary/acquisition.json') if 'sha256' in e]
for base in ['arveson1972','hartz-devries2026']:e=read(D/'primary'/(base+'-acquisition.json'));acquired.append(dict(e,file=base+'.pdf'))
assert len(acquired)==3
for e in acquired:b=(D/'primary'/e['file']).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
primary=s['primary_semantic_reads'];assert len(primary)==4
primary_extents=0
for e in primary:
 b=(D/e['file']).read_bytes();assert len(b)>0
 if 'read_bytes' in e:
  ranges=e['read_bytes'] if isinstance(e['read_bytes'][0],list) else [e['read_bytes']]
  for lo,hi in ranges:assert 0<=lo<hi<=len(b);primary_extents+=1
 else:assert e['file']=='primary/paulsen1984-web-section2.txt' and '109--303' in e['read_extent']
history=read(D/'history-selections.json');assert len(history)==8;sections=0
for e in history:
 lo,hi=e['bytes']
 with (PROJECT/e['path']).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
 assert b==(D/'history-selected'/e['local']).read_bytes() and sha(b)==e['selection_sha256']
 for sub in e['individually_selected_contiguous_sections']:
  a,z=sub['original_bytes'];assert lo<=a<z<=hi and sha(b[a-lo:z-lo])==sub['sha256'];sections+=1
with (PROJECT/'sources/CONTENTS.md').open('rb') as f:f.seek(550877);b=f.read(552844-550877)
assert b==(D/'source325-catalogue.txt').read_bytes() and sha(b)=='4d7016e17e536f0cad6f1f94a86b77f33e264530b2a414014c20f076dd149348'
e=read(D/'direct-reading.json');lo,hi=e['acceptance_range']
with (PROJECT/'frontier/NEW-TEN-2026-10-14.md').open('rb') as f:f.seek(lo);b=f.read(hi-lo)
assert [lo,hi]==[4801,6347] and sha(b)==e['acceptance_sha256']=='f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'
controls=[]
with tempfile.TemporaryDirectory(prefix='r201-control-',dir=P) as tmp:
 T=Path(tmp);shutil.copytree(R/'controls/tiny-copied-fixture',T/'packet');shutil.copy2(R/'controls/REPORT-control.txt',T/'REPORT.txt');k=T/'packet';r=T/'REPORT.txt';aa={'FINAL':sha((k/'FINAL.md').read_bytes()),'MANIFEST':sha((k/'MANIFEST.json').read_bytes()),'REPORT':sha(r.read_bytes())}
 def check(name,wanted,override=None):
  q=verify(k,r,override or aa);ok=q.returncode==0;assert ok==wanted,(name,q.stdout,q.stderr);controls.append({'case':name,'accepted':ok,'expected':wanted})
 check('clean',True);payload=k/'copied-bytes.bin';b=payload.read_bytes();m0=stat.S_IMODE(payload.stat().st_mode);payload.chmod(0o600);payload.write_bytes(b+b'x');payload.chmod(m0);check('one-byte-addition',False);payload.chmod(0o600);payload.write_bytes(b);payload.chmod(m0);payload.chmod(m0^0o100);check('mode-only-change',False);payload.chmod(m0);extra=k/'unselected.txt';extra.write_text('control\n');check('unselected-member',False);extra.unlink();wrong=dict(aa);wrong['MANIFEST']='0'*64;check('wrong-detached-manifest',False,wrong)
assert observe()==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'selected_files':54,'selected_directories':12,'selected_bytes':sum(e['bytes'] for e in m['files']),'canonical_blobs':10,'canonical_reading_bindings':8,'comparator_bindings':5,'lean_documentation_binding':1,'primary_pdf_bindings':3,'primary_reading_records':4,'primary_byte_extents':primary_extents,'primary_web_text_reproduction':1,'history_exact_spans':8,'history_individual_sections':sections,'catalogue_acceptance_bindings':2,'copied_controls':controls,'root_files':sum(e['type']=='file' for e in before.values()),'author_bytes_modes_unchanged':True,'limits':'Receipt binding and artifact verification are not semantic reading, numerical replay or mathematical grades. Paulsen reproduction is retained rather than independently reacquired.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');(P/'replay.json').chmod(0o600);print(json.dumps(out,indent=2))
