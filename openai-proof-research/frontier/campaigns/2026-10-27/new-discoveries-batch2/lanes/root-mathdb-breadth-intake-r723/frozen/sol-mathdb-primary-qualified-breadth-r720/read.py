exec(__import__('pathlib').Path(__file__).with_name('bind.py').read_text().split('for n in ')[0])
ids=set(j(I/'reserved-ids-r720.json')['ids']);out=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   out.append({'corpus_chunk':str(p.relative_to(C)),'corpus_line':n,'record':r,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50
(P/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for i,e in enumerate(out):
 r=e['record'];print(i,r['mathdb_id'],r['title']);print(r['statement']);print('SOURCE',r.get('source'),r.get('references'));print('FIELDS',list(r) if i==0 else '')
