from pathlib import Path
import json,hashlib,datetime,re
O=Path(__file__).parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
extra=[]
root=O.parents[5] # not used to infer source paths
repo=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
for p in [repo/'sources/upstream.json',repo/'sources/CONTENTS.md',repo/'sources/preprints-tree.json',O.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 q=O/'inputs'/('catalogue-'+p.name);q.write_bytes(p.read_bytes());assert h(p)==h(q);extra.append(dict(original=str(p),copy=str(q),sha256=h(q)))
for p in list(O.parents):
 a=p/'AGENTS.md'
 if a.exists():
  q=O/'inputs'/('instructions-'+str(len(extra))+'.md');q.write_bytes(a.read_bytes());assert h(a)==h(q);extra.append(dict(original=str(a),copy=str(q),sha256=h(q)));print('INSTRUCTION',a,a.read_text()[:500])
(O/'extra-bindings.json').write_text(json.dumps(extra,indent=2))
versions=[]
bind=json.loads((O/'body-bindings.json').read_text())
receipt=[]
for p in (O/'inputs').glob('*http.jsonl'):
 for line in p.read_text().splitlines():
  try:receipt.append(json.loads(line))
  except json.JSONDecodeError:pass
for r in bind:
 if not r['copy'].endswith('.pdf'):continue
 matches=[v for v in receipt if v.get('sha256')==r['sha256']]
 versions.append(dict(file=r['copy'],sha256=r['sha256'],inherited_http=matches,coverage='Tyszka target definitions, Conj3/4/5, Theorems11/12/Lemma4; overlapping conjectures; Frenkel3.1-3.4; Akman2.3/2.4 and4.1 proof; Frank4.2/5.1/5.2/Section6; Kellerhals-Peters abstract only, not a competing proof clearance'))
for key in ['tyszka-current','tyszka-overlap-current','frenkel-current','akman-current','frank-current','1108.4078-abs']:
 p=O/'retrieved'/key;t=p.read_text();a=t.find('Submission history');z=t.find('Full-text links',a);section=re.sub('<[^>]*>',' ',t[a:z]);section=re.sub(r'\s+',' ',section)
 versions.append(dict(metadata_file=str(p),sha256=h(p),history=section))
versions.append(dict(file='retrieved/1108.4078v2.pdf',sha256=h(O/'retrieved/1108.4078v2.pdf'),url='https://arxiv.org/pdf/1108.4078v2',coverage='Actual Theorems1.1/1.2, Sections2-5 proof read; v2 4May2012, first20Aug2011. Public rational exact-equation resolution; not original residual/G claims.'))
(O/'versions.json').write_text(json.dumps(versions,indent=2))
terms=['Tyszka','Frenkel','division graph','Integrated Veto','1108.4078','0702558']
(O/'catalogue-screen.json').write_text(json.dumps({p.name:{t:p.read_text().lower().count(t.lower()) for t in terms} for p in (O/'inputs').glob('catalogue-*') if p.suffix in ['.md','.json']},indent=2))
(O/'provenance.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scientific_freeze':['freeze.json','body-bindings.json','extra-bindings.json'],'history':'history-screen.json immutable REFERENCES verified, no recursive copies','administration':'ledger and prior context snapshot only; live mutable NEXT/ledger not bound as scientific dependencies','guard':'512MiB AS and sampled group RSS, CPU210s, wall230s; unchanged','count':'root only;9 additional/39 total,next40','proof_status':'complete ordinary classical bridges; no novelty nomination or independent acceptance','manifest_exclusions':['finalmanifest.json','verification-receipt.json']},indent=2))
files={str(p.relative_to(O)):h(p) for p in sorted(O.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
(O/'finalmanifest.json').write_text(json.dumps({'excludes_explicitly':['finalmanifest.json','verification-receipt.json'],'files':files},indent=2))
print('FINAL FILES',len(files))
