exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('out=[entry')[0])
refs=j(P/'initial-bindings.json')
for d in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 for p in (L/d).iterdir():
  if p.is_file():refs.append(entry(p))
(P/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
cov=j(I/'coverage-delta.json');rs=j(I/'active-breadth-reservations.json');ids=set(j(I/'reserved-ids-r692.json')['ids']);assert len(cov)==8183
sets=[set(r['ids']) for r in rs];assert len(sets)==3
for a,s in enumerate(sets):
 assert not set(map(str,s))&set(cov);assert not s&set(j(I/'reserved-ids-r692.json')['protected_ids'])
 for t in sets[a+1:]:assert not s&t
assert ids==sets[2]
records=[]
for e in j(C/'manifest.json')['files']:
 if not e['path'].startswith('corpus/'):continue
 for n,line in enumerate((C/e['path']).open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   records.append({'mathdb_id':r['mathdb_id'],'corpus_path':e['path'],'corpus_line':n,'statement_utf8':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(records)==50
records.sort(key=lambda r:r['mathdb_id']);(P/'literal-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
print('Disjointness PASS; exact 50 extracted.');print('record keys',records[0]['record'].keys())
for r in records:print('\nID',r['mathdb_id'],'\n',r['statement_utf8'],'\nSOURCE',r['record'].get('references',r['record'].get('source','')))
