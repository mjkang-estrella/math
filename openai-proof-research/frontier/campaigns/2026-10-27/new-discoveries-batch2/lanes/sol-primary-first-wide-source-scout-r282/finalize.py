from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
B=L.parent.parent
R=B.parents[3]
def sha(d):return hashlib.sha256(d).hexdigest()
admin=[]
for name,p in [('batch-AGENTS.md',B/'AGENTS.md'),('ancestor-AGENTS.md',R/'AGENTS.md'),('ledger.json',B/'ledger.json'),('prior-campaign-context.json',B/'prior-campaign-context.json'),('r279-STATUS.md',L.parent/'root-scout-r279-disposition/STATUS.md')]:
 d=p.read_bytes();(L/'administrative'/name).write_bytes(d);admin.append({'original':str(p),'copy':name,'sha256':sha(d),'bytes':len(d),'scope':'administrative snapshot only'})
(L/'administrative-snapshot.json').write_text(json.dumps(admin,indent=2))
ledger=json.loads((B/'ledger.json').read_text());assert [ledger[k]for k in ['accepted_count','total_accepted_count','next_global_outcome_number']]==[9,39,40]
ctx=json.loads((B/'prior-campaign-context.json').read_text())
print('administrative context parsed',list(ctx),'counts 9/39/40')
bindings=[]
terms={'sun.txt':['Conjecture 2.16.','Conjecture 2.17.','Conjecture 3.1.','Conjecture 3.3.'],'mcnamara.txt':['Conjecture 4.1.','Conjecture 5.3.','Conjecture 5.5.','Conjecture 7.1.','Conjecture 7.4.'],'negative.txt':['Question 3.1.','Question 3.4.','Question 4.1.','Definition 4.1.','Proposition 4.15.'],'sequence.txt':['Conjecture 3.1.','Remark 1.4.','Conjecture 3.8.'],'branden.txt':['Proof of Conjecture 1.1.'],'finitefield.txt':['Theorem 1.1.','Lemma 2.1.']}
for name,labels in terms.items():
 p=L/'primary'/name;d=p.read_bytes();s=d.decode();h=sha(d)
 for lab in labels:
  pos=s.find(lab);assert pos>=0
  bindings.append({'file':str(p),'sha256':h,'label':lab,'offset':pos,'page':s[:pos].count('\f')+1,'excerpt':s[max(0,pos-100):pos+2500]})
 assert sha(p.read_bytes())==h
p=L/'primary/denominators.txt';d=p.read_bytes();s=d.decode();bindings.append({'file':str(p),'sha256':sha(d),'label':'Final questions','page':54,'excerpt':s.split('\f')[53]});assert sha(p.read_bytes())==sha(d)
(L/'source-bindings.json').write_text(json.dumps(bindings,indent=2))
refs={}
for line in (L/'bindings.jsonl').open():
 b=json.loads(line);refs[b['path']]={'sha256':b['sha256'],'bytes':b['bytes']}
(L/'referenced-originals.json').write_text(json.dumps(refs,indent=2))
access=[json.loads(z)for z in (L/'access.jsonl').read_text().splitlines()]
prov={'lane':L.name,'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'counts':'9 additional /39 total / next40; unchanged','discovery_credit_requested':0,'status':'restricted helpers and bounded research holds only','primary_access':access,'source_bindings':'source-bindings.json','scientific_freeze_log':'bindings.jsonl','original_reference_inventory':'referenced-originals.json','administrative':'administrative-snapshot.json','resource_caps':{'AS_bytes':512*1024**2,'groupRSS_bytes':512*1024**2,'CPU_seconds':210,'wall_seconds':230},'guard':'../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','scope_limits':['Current registry head not cleared; denied routes parked','No exhaustive external citation audit','No journal/preprint line-by-line equivalence','Cached proof publication chronology unverified','One bytecode-env-variable typo documented in progress.md'],'ranked_holds':['van Doorn harmonic denominator equivalence','Sun cumulative finite-field counts','Sun generalized harmonic root log-convexity'],'failures':'progress.md','manifest_exclusions':['MANIFEST.json','verification-receipt.json']}
(L/'provenance.json').write_text(json.dumps(prov,indent=2))
manifest={}
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']:
  d=p.read_bytes();manifest[str(p.relative_to(L))]={'sha256':sha(d),'bytes':len(d)}
(L/'MANIFEST.json').write_text(json.dumps(manifest,indent=2))
print('manifest files',len(manifest),'scientific originals',len(refs))
