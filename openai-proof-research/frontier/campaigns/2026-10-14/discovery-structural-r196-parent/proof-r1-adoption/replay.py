#!/usr/bin/env python3
"""Read-only parent adoption replay; mutate only temporary copied fixtures here."""
from pathlib import Path
import datetime,hashlib,json,os,shutil,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;C=P.parents[1];PROJECT=C.parents[2];R=C/'structural-r196-proof-r1';A=C/'fresh-structural-discovery-r196'
anchors={'FINAL.md':'624bd0857ac63a81126fc66ee1a684a6146813303a11511227709fa2329460ca','MANIFEST.json':'34ae9dc53e80f9c7be5925768f53076d1e40b0c410fcb23ade908b4e85a7a318','REPORT.md':'9be39514e35a6a20010b4b413b53b0a4d6ecc45dd93067b1acf67dd26da031cc'}
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda f:json.loads(f.read_text())
def inventory(root):
 result={}
 for p in [root,*root.rglob('*')]:
  s=p.lstat();assert not p.is_symlink()
  e={'mode':stat.S_IMODE(s.st_mode),'kind':'dir' if p.is_dir() else 'file'}
  if p.is_file():e.update(bytes=s.st_size,sha256=sha(p.read_bytes()))
  result[p.relative_to(root).as_posix()]=e
 return result
before=inventory(R);author=inventory(A)
def verify(root,an):
 cmd=[sys.executable,'-I','-B',str(R/'verify_packet.py'),'--root',str(root),'--final-sha256',an['FINAL.md'],'--manifest-sha256',an['MANIFEST.json'],'--report-sha256',an['REPORT.md']]
 return subprocess.run(cmd,capture_output=True,text=True,timeout=20)
v=verify(R,anchors);assert v.returncode==0,(v.stdout,v.stderr);verification=json.loads(v.stdout);assert verification['selected_files']==142
m=read(R/'MANIFEST.json');assert set(before)==set(m['selection'])|set(m['directories'])|set(m['detached_modes'])
treefile=PROJECT/'sources/preprints-tree.json';tb=treefile.read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(treefile);assert not tree['truncated'];lookup={x['path']:x for x in tree['tree']}
canonical=read(R/'private/canonical-authentication.json')
for e in canonical:
 b=(R/e['review_copy']).read_bytes();assert b==(PROJECT/e['original']).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'];blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==e['git_blob'];path=e['upstream_path'];key=path if path in lookup else path.removeprefix('preprints/');assert lookup[key]['sha']==blob
 assert stat.S_IMODE((PROJECT/e['original']).stat().st_mode)==e['mode']
for e in read(R/'private/primary-authentication.json'):
 b=(R/e['review_copy']).read_bytes();assert b==(PROJECT/e['original']).read_bytes() and sha(b)==e['sha256'] and len(b)==e['bytes'];assert stat.S_IMODE((PROJECT/e['original']).stat().st_mode)==e['mode']
for e in read(R/'private/history-authentication.json'):
 b=(PROJECT/e['original']).read_bytes()[slice(*e['byte_extent'])];assert b==(R/e['review_copy']).read_bytes() and sha(b)==e['sha256']
for file in ['primary-retrieval.json','primary-text-replay.json']:
 for e in read(R/'private'/file):
  b=(R/e['path']).read_bytes();assert sha(b)==e['sha256'] and len(b)==e['bytes']
ledger=read(R/'private/reading-ledger.json')
for e in ledger['semantic_source_primary_history_reads']:
 b=(R/e['review_copy']).read_bytes();assert len(b)==e['file_bytes'] and sha(b)==e['sha256'];s=b.decode()
 for br,cr in zip(e['copy_byte_extents'],e['copy_utf8_character_extents']):assert b[slice(*br)].decode()==s[slice(*cr)]
for e in ledger['direct_reads']:
 b=(PROJECT/e['path']).read_bytes();br=e['byte_extent']
 if 'sha256' in e:assert sha(b)==e['sha256']
 else:assert sha(b[slice(*br)])==e['sha256_selected_bytes']
 if 'utf8_character_extent' in e:assert b[slice(*br)].decode()==b.decode()[slice(*e['utf8_character_extent'])]
for e in read(R/'private/author-anchor-baseline.json'):
 p=PROJECT/e['path'];b=p.read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'] and stat.S_IMODE(p.stat().st_mode)==e['mode']
old=read(P.parent/'observed-root.json');current={k:{x:v for x,v in e.items() if x!='kind'} for k,e in author.items() if e['kind']=='file'};assert current==old
controls=[];base=R/'private/controls/baseline';ca=read(base/'ANCHORS.json')
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as td:
 w=Path(td)/'fixture'
 def check(name,mut=None,wrong=None,expected=1):
  if w.exists():shutil.rmtree(w)
  shutil.copytree(base,w)
  if mut:mut(w)
  result=verify(w,wrong or ca);assert result.returncode==expected,(name,result.stdout,result.stderr)
  controls.append({'test':name,'exit_code':result.returncode,'expected_exit':expected})
 check('untampered_copy',expected=0)
 check('extra_file',lambda w:(w/'extra').write_text('extra'))
 check('missing_file',lambda w:(w/'data/payload.txt').unlink())
 check('file_mode_change',lambda w:(w/'data/payload.txt').chmod(0o600))
 check('directory_mode_change',lambda w:(w/'data').chmod(0o755))
 check('extra_empty_directory',lambda w:(w/'extra-dir').mkdir())
 check('selected_byte_change',lambda w:(w/'data/payload.txt').write_text('changed'))
 check('detached_mode_change',lambda w:(w/'REPORT.md').chmod(0o600))
 check('symlink',lambda w:(w/'link').symlink_to('data/payload.txt'))
 check('wrong_explicit_anchor',wrong={**ca,'REPORT.md':'0'*64})
 check('altered_anchor_carrier',lambda w:(w/'ANCHORS.json').write_text('{}\n'))
 check('anchor_carrier_extra_whitespace',lambda w:(w/'ANCHORS.json').write_text((w/'ANCHORS.json').read_text()+'\n'))
assert inventory(R)==before and inventory(A)==author
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':verification,'review_sha256':sha((R/'REVIEW.md').read_bytes()),'selected_files':142,'selected_bytes':sum(e['bytes'] for e in m['selection'].values()),'canonical_blobs':len(canonical),'primary_texts':6,'fresh_primary_pdf_and_extraction_receipts':6,'history_spans':3,'reading_record_bindings_matched':True,'controls':controls,'author_full_inventory_matches_intake':True,'author_and_reviewer_bytes_modes_unchanged':True,'limitations':ledger['limits']+['Reviewer lacked an independent initial history-mode receipt; byte spans match. Parent checked receipts/byte bindings without claiming its own semantic source/primary reread.']}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['controls','limitations','anchors']},indent=2));print('copied_controls',len(controls))
