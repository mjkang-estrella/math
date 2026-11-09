exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('out=[ent')[0])
# Bind required actual r304 originals before reading.
b=json.loads((D/'flat-bindings.json').read_text())
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 p=L/'root-mathdb-accepted-exclusions-r304'/n;b.append(ent(p))
(D/'flat-bindings.json').write_text(json.dumps(b,indent=2)+'\n')
R=json.loads((I/'reserved-ids.json').read_text()); C=json.loads((I/'coverage-delta.json').read_text());A=json.loads((I/'active-breadth-reservations.json').read_text());Q=json.loads((I/'queue.json').read_text())
assert len(C)==4933 and set(R['ids'])=={x['mathdb_id'] for x in Q}
seen=set()
for x in A:
 s=set(x['ids']);assert len(s)==50 and not(s&seen) and not(s&set(map(int,C))) and not(s&set(R['protected_ids']));seen|=s
out=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in R['ids']:
   out.append({'record':r,'chunk':str(p),'line':n,'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50
(D/'assigned-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
(D/'reading.txt').write_text('\n\n'.join(str(x['record']['mathdb_id'])+' '+x['record']['title']+'\n'+x['record']['statement']+'\nSOURCE '+str(x['record']['source_url']) for x in out))
print((D/'reading.txt').read_text())
