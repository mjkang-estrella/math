from pathlib import Path
import hashlib,json,shutil,zipfile
R=Path(__file__).resolve().parent; P=R.parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs=[]
for lane,parts in {'xor-magic-formal-r5':['xor-magic-r5-source.zip','formal','results.json','SUMMARY.md','statement-correspondence.md','replay.py','receipts','tools','modules.json','audit-groups.json'], 'xor-magic-focused-r1':['PROOF.md','PRIOR-ART.md','outputs','sources','receipts'], 'xor-magic-review-r1':['review.json','REVIEW.md','work/web','receipts'], 'expanded-corpus-r90':['raw/372205.jsonl']}.items():
 for s in parts:
  p=P/lane/s
  if p.is_dir(): inputs.extend(x for x in p.rglob('*') if x.is_file())
  else: inputs.append(p)
inputs.extend((P/'expanded-corpus-r90/sources').glob('2512.19278.*'))
inputs.append(P/'xor-magic-root-ruling-r1.json')
bind={str(p.relative_to(P)):h(p) for p in sorted(set(inputs))}
(R/'receipts').mkdir(exist_ok=True)
(R/'receipts/frozen-before.json').write_text(json.dumps(bind,indent=2)+'\n')
assert h(P/'xor-magic-formal-r5/xor-magic-r5-source.zip')=='d73964ef74903d789f152b0835994549859447377d481cbe19ff94e1f87937da'
D=R/'dossier'; D.mkdir(exist_ok=True)
for part in ['formal','tools','negative']:
 shutil.copytree(P/'xor-magic-formal-r5'/part,D/part,ignore=shutil.ignore_patterns('*.olean','*.ilean','__pycache__'))
for part in ['replay.py','modules.json','audit-groups.json','statement-correspondence.md']:
 shutil.copy2(P/'xor-magic-formal-r5'/part,D/part)
s=(D/'replay.py').read_text().replace("os.environ.clear()","actual_home=os.environ['HOME']\nos.environ.clear()").replace("HOME=str(root/'home')","HOME=actual_home")
(D/'replay.py').write_text(s)
s=(D/'tools/bounded.py').read_text().replace("if line.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:')):","if line.startswith('Rss:'):").replace("'sampled_private_rss_bytes':peak","'sampled_aggregate_rss_bytes':peak,'cpu_limit_seconds':120,'wall_limit_seconds':140,'rss_limit_bytes':6*1024**3,'cpu_affinity':sorted(os.sched_getaffinity(0))[:2]")
(D/'tools/bounded.py').write_text(s)
for lane in ['xor-magic-focused-r1','xor-magic-review-r1']:
 for part in (['PROOF.md','PRIOR-ART.md','outputs','sources','receipts'] if 'focused' in lane else ['REVIEW.md','review.json','work/web']):
  p=P/lane/part; dest=D/'evidence'/lane/part; dest.parent.mkdir(parents=True,exist_ok=True)
  if p.is_dir(): shutil.copytree(p,dest)
  else: shutil.copy2(p,dest)
for p in (P/'expanded-corpus-r90/sources').glob('2512.19278.*'):
 dest=D/'evidence/primary'/p.name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dest)
shutil.copy2(P/'expanded-corpus-r90/raw/372205.jsonl',D/'mathdb-372205.jsonl')
shutil.copy2(P/'xor-magic-root-ruling-r1.json',D/'evidence/root-ruling.json')
for name in ['xor-16-5.json','xor-16-7.json','xor-32-9.json']:
 dest=D/'evidence/expanded-outputs'/name; dest.parent.mkdir(exist_ok=True);shutil.copy2(P/'expanded-corpus-r90/outputs'/name,dest)
(R/'receipts/lean-identity.json').write_text(json.dumps({p.name:h(p) for p in (D/'formal').glob('*.lean')},indent=2)+'\n')
# Bind every source replay member, not built artifacts.
manifest={str(p.relative_to(D)):h(p) for p in sorted(D.rglob('*')) if p.is_file()}
(D/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(R/'xor-magic-manuscript-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(D.rglob('*')):
  if p.is_file(): z.write(p,p.relative_to(D))
E=R/'fresh-replay';E.mkdir()
with zipfile.ZipFile(R/'xor-magic-manuscript-source.zip') as z:
 for i in z.infolist():
  p=Path(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and not (i.external_attr>>16)&0o170000==0o120000
 z.extractall(E)
(R/'receipts/extraction.json').write_text(json.dumps({'safe':True,'archive_sha256':h(R/'xor-magic-manuscript-source.zip'),'members':len(manifest)+1,'existing_oleans':False},indent=2)+'\n')
print('prepared',len(bind),'frozen files',len(list((D/'formal').glob('*.lean'))),'Lean modules')
