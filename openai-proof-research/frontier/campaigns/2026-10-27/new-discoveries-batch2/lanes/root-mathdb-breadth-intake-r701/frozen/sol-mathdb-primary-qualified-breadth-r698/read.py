exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('refs={}')[0])
q=j(I/'queue-r698.json');ids={r['mathdb_id'] for r in q};assert len(ids)==50 and ids==set(j(I/'reserved-ids-r698.json')['ids'])
cov=j(I/'coverage-delta.json');assert len(cov)==8333
seen=set()
for a in j(I/'active-breadth-reservations.json'):
 s=set(a['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(a['protected_ids']);seen|=s
out=[]
for e in j(C/'manifest.json')['files']:
 if not e['path'].startswith('corpus/'):continue
 for n,line in enumerate((C/e['path']).open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   out.append({'chunk':e['path'],'line':n,'record':r});print('\nID',r['mathdb_id'],r['title'],'\n',r['statement'],'\nSOURCE',r['source_url'],'REF',r['references'])
assert len(out)==50
(P/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print('CONTEXT')
for p in [I/'adjudications.json',I/'hypothesis-queue.json',L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 a=j(p);print(p.name, json.dumps(a,ensure_ascii=False)[:6000])
print('BOUND REQUIRED',*[e['path'] for e in j(P/'flat-bindings.json') if 'r304/' in e['path'] or 'r363/' in e['path']],sep='\n')
