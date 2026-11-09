exec(open(__file__.replace('extract.py','freeze.py')).read().split('# Freeze intake')[0])
q=json.loads((I/'queue.json').read_text());ids={x['mathdb_id'] for x in q};r=json.loads((I/'reserved-ids.json').read_text());assert ids==set(r['ids']) and len(ids)==50 and len(set(r['other_active_reservations']))==100 and not ids&set(r['other_active_reservations']) and not ids&{372627,372628,368940,404067,364119}
rows=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  x=json.loads(line)
  if x.get('mathdb_id',x.get('id')) in ids:rows.append({'chunk':str(p),'line':n,'record':x})
assert len(rows)==50
(O/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(rows[0],ensure_ascii=False,indent=2))
