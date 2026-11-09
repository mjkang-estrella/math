exec(open(__file__.replace('read.py','preflight.py')).read().split('for name in')[0])
a=L/'root-mathdb-breadth-intake-r435'; ids=json.loads((a/'reserved-ids.json').read_text()); wanted=set(ids['ids']);q=json.loads((a/'queue.json').read_text()); old=json.loads((a/'coverage-delta.json').read_text());assert len(wanted)==50 and len(old)==2283;assert wanted=={x['mathdb_id'] for x in q};assert not wanted&set(ids['other_active_reservations']);assert not wanted&set(map(int,old));assert not wanted&{372627,372628,368940,404067,364119}
records=[];loc=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 with p.open() as f:
  for n,line in enumerate(f,1):
   r=json.loads(line)
   if r['mathdb_id'] in wanted:records.append(r);loc.append({'id':r['mathdb_id'],'original':str(p),'line':n})
assert len(records)==50
records.sort(key=lambda x:x['mathdb_id']);(O/'records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n');(O/'record-locations.json').write_text(json.dumps(loc,indent=2)+'\n')
(O/'literal-reading.txt').write_text('\n\n'.join(str(r['mathdb_id'])+' '+r['title']+'\n'+r['statement']+'\nSOURCE '+str(r['source_url'])+'\nREF '+str(r['references']) for r in records))
print((O/'literal-reading.txt').read_text())
