exec(open(str(__file__).replace('extract.py','freeze.py')).read().split('refs=[]')[0])
ids=set(load(I/'reserved-ids.json')['ids']); rows=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:rows.append({'record':r,'original_chunk':str(p),'original_line':n})
assert len(rows)==50
(O/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2))
with (O/'literal-statements.txt').open('w') as f:
 for a in rows:
  r=a['record'];f.write(f"\nID {r['mathdb_id']} {r['title']}\n{r['statement']}\nSOURCE {r.get('source_url')} {r.get('source_name')}\n")
print('extracted',len(rows))
