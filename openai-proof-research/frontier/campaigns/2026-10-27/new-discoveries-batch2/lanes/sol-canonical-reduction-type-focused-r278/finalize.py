from pathlib import Path
import json,hashlib,datetime,xml.etree.ElementTree as E
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(name,obj):(L/name).write_text(json.dumps(obj,indent=2)+'\n')
refs=json.loads((L/'source-bindings.json').read_text())
bad=[]
for r in refs:
 h=sha(Path(r['path']));r['sha256_after']=h
 if h!=r['sha256']:bad.append(r['path'])
write('source-bindings.json',refs)
access=[json.loads(s) for s in (L/'access.jsonl').read_text().splitlines()]
for r in access:
 if 'sha256' in r:
  p=L/r['path'];assert sha(p)==r['sha256']
  if 'text_sha256' in r:assert sha(p.with_suffix('.txt'))==r['text_sha256']
assert not bad, bad
ns={'a':'http://www.w3.org/2005/Atom'};chron=[]
for name in ['versions.xml','canonical.xml','specialist.xml']:
 for e in E.fromstring((L/'sources'/name).read_bytes()).findall('a:entry',ns):
  chron.append(dict(query=name,**{k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated']}))
write('chronology.json',dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),entries=chron,priority='bounded query chronology only; registry head unknown'))
write('progress.json',dict(status='HOLD: no full proof or counterexample',completed=['source scope','early semantic gates','actual proof-body comparisons','universal restricted case','two-box classification','bounded structural diagnostics','final bindings'],missing='universal multi-box admissibility lemma',proposed_credit=0,counts=dict(additional=9,total=39,next=40,owner='root'),no_PROOF_md=True))
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
write('provenance.json',dict(lane=str(L),solo=True,children=0,writes='assigned lane only',guard=dict(path=str(guard),sha256=sha(guard),AS_bytes=512*1024**2,group_RSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230,OPENBLAS_NUM_THREADS=1,OMP_NUM_THREADS=1,PYTHONDONTWRITEBYTECODE=1),source_policy='frozen files or immutable references before scientific reading, originals verified again after; no recursive history copies',access_policy='no prohibited GitHub/ScienceDirect/Google challenge routes; no bypass or denied-route retries',registry='UNKNOWN; cached bodies and bounded arXiv queries do not clear current registry',scientific_result='restricted unique-W-factorization case only; no source resolution or novelty nomination',binding_checks=len(refs),binding_failures=bad))
manifest=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']:
  manifest.append(dict(path=str(p.relative_to(L)),sha256=sha(p),size=p.stat().st_size))
write('MANIFEST.json',dict(excludes=['MANIFEST.json','verification-receipt.json'],files=manifest))
print(json.dumps(dict(manifest_files=len(manifest),immutable_references=len(refs),changed_references=bad)))
