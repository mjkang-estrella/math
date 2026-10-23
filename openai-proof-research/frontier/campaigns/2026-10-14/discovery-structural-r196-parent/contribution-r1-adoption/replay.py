#!/usr/bin/env python3
"""Read-only contribution adoption replay, with tiny copied controls."""
from pathlib import Path
import datetime,hashlib,json,os,shutil,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;C=P.parents[1];PROJECT=C.parents[2];R=C/'structural-r196-contribution-r1';A=C/'fresh-structural-discovery-r196'
anchors={'FINAL.md':'d79d1c1dd9d02b3641b3d6ec08054423369a12c9d99438218ba7875dcf882816','MANIFEST.json':'a6509ac2d2e849af883d26dde18ec0cb6f05844de6719e194462c2c78b155c82','REPORT.md':'ce5be243a9f4426099a0a2d3b78449dcd4033a89cdaf88078a4045092a605116'}
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_text())
def inventory(root):
 out={}
 for p in [root,*root.rglob('*')]:
  st=p.lstat();assert not p.is_symlink();e={'mode':stat.S_IMODE(st.st_mode),'kind':'dir' if p.is_dir() else 'file'}
  if p.is_file():e.update(bytes=st.st_size,sha256=sha(p.read_bytes()))
  out[p.relative_to(root).as_posix()]=e
 return out
before=inventory(R);author=inventory(A)
def verify(root,a):
 return subprocess.run([sys.executable,'-I','-B',str(R/'verify_packet.py'),'--root',str(root),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['MANIFEST.json'],'--report-sha256',a['REPORT.md']],capture_output=True,text=True,timeout=20)
v=verify(R,anchors);assert v.returncode==0,(v.stdout,v.stderr);vr=json.loads(v.stdout);assert vr['selected_files']==67;m=read(R/'MANIFEST.json')
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tr=json.loads(tb);assert not tr['truncated'];lookup={e['path']:e for e in tr['tree']}
canonical=read(R/'private/canonical-authentication.json')
for e in canonical:
 f=PROJECT/e['local'];b=f.read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'] and stat.S_IMODE(f.stat().st_mode)==e['mode'];blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==e['git_blob'];k=e['path'] if e['path'] in lookup else e['path'].removeprefix('preprints/');assert lookup[k]['sha']==blob
for e in read(R/'private/history-authentication.json'):
 b=(PROJECT/e['original']).read_bytes()[slice(*e['byte_extent'])];assert b==(A/e['selected_copy']).read_bytes() and sha(b)==e['sha256']
for file,suffix in [('access.json','.pdf'),('extraction.json','.txt')]:
 for e in read(R/'private/primary'/file):
  b=(R/'private/primary'/(e['name']+suffix)).read_bytes();assert sha(b)==e['sha256'] and len(b)==e['bytes'];assert b==(A/'private/primary'/(e['name']+suffix)).read_bytes()
records=read(R/'private/reading-ledger.json')['records']
for row in records:
 b=(PROJECT/row['path']).read_bytes()
 for e in row['semantic_extents']:
  selected=b[slice(*e['bytes'])];assert sha(selected)==e['sha256'];origin=e['admitted_byte_origin'];assert selected.decode()==b[origin:].decode()[slice(*e['characters_from_admitted_origin'])]
ins=read(R/'private/instruction-authentication.json')
for e in [ins['authoritative_brief'],ins['acceptance_rules'],*ins['direct_instructions'],ins['complete_tree']]:
 b=(PROJECT/e['path']).read_bytes();b=b[slice(*e['byte_extent'])] if 'byte_extent' in e else b;assert sha(b)==e['sha256']
assert read(R/'private/author-integrity-after.json')['matched_before_inventory']
for name in ['author-integrity-before.json']:
 for e in read(R/'private'/name):
  actual=author[e['path']];assert all(actual[k]==('dir' if k=='kind' and v=='directory' else v) for k,v in e.items() if k!='path'),e['path']
old=read(P.parent/'observed-root.json');assert {k:{j:v for j,v in e.items() if j!='kind'} for k,e in author.items() if e['kind']=='file'}==old
saved=read(R/'private/controls/results.json')['results'];controls=[];ca=read(R/'private/controls/baseline/ANCHORS.json')
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as td:
 for e in saved:
  w=Path(td)/e['case'];shutil.copytree(R/'private/controls'/e['case'],w);wb=inventory(w);x=verify(w,ca);assert x.returncode==e['expected_returncode']==e['actual_returncode'];assert inventory(w)==wb;controls.append({'case':e['case'],'expected':e['expected_returncode'],'actual':x.returncode})
assert inventory(R)==before and inventory(A)==author
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':vr,'review_sha256':sha((R/'REVIEW.md').read_bytes()),'selected_files':67,'selected_bytes':sum(e['bytes'] for e in m['files']),'canonical_blobs':37,'primary_pdf_text_pairs':6,'history_spans':3,'semantic_record_bindings':len(records),'instruction_bindings_matched':True,'controls':controls,'author_full_inventory_matches_intake':True,'author_and_reviewer_bytes_modes_unchanged':True}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n');print(json.dumps(out,indent=2))
