import json,pathlib,re,hashlib,subprocess,datetime
b=pathlib.Path(__file__).resolve().parent.parent; o=b/'analysis-r3'; ids=[325507,347029,374935,352819]
pool=json.load(open(b/'analysis/selection-pool.json')); records=[x for x in pool if x['mathdb_id'] in ids]
assert len(records)==4 and all(x%3==1 for x in ids)
json.dump(records,open(o/'literal-records.json','w'),indent=2)
hits=[]; context=[]
root=pathlib.Path('openai-proof-research')
for p in root.rglob('*'):
 if not p.is_file() or p.stat().st_size>1500000 or 'analysis-r3' in p.parts or any(t in p.parts for t in ['corpus','sources','.git']): continue
 if not re.search(r'ledger|reservation|status|REPORT|REVIEW|results|decision|rejection',p.name,re.I):continue
 try:t=p.read_text()
 except:continue
 found=[i for i in ids if re.search(r'(?<!\d)'+str(i)+r'(?!\d)',t)]
 if found:hits.append({'path':str(p),'ids':found})
 if p.name in ['ledger.json','reservation.json','status.json']:context.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
json.dump({'hits':hits,'context':context},open(o/'history-screen.json','w'),indent=2)
json.dump({'lane':'analysis-r3','reserved_ids':ids,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'local reservation only; do not duplicate across lanes'},open(o/'reservation.json','w'),indent=2)
print(hits)
