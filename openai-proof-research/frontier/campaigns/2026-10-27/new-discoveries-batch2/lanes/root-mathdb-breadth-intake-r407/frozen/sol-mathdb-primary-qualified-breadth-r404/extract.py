from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent;B=L.parent;R=B/'root-mathdb-breadth-intake-r403';C=B/'pi-mathdb-full-corpus-inventory-r301'
doc=json.loads((L/'bindings.json').read_text())
for e in json.loads((B/'root-mathdb-accepted-exclusions-r304/bindings.json').read_text()):
 p=Path(e['original']);b=p.read_bytes();doc['refs'][str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
(L/'bindings.json').write_text(json.dumps(doc,indent=2)+'\n')
a=json.loads((R/'reserved-ids.json').read_text());ids=set(a['ids']); reviewed=set(map(int,json.loads((R/'coverage-delta.json').read_text())))
assert len(ids)==50 and len(reviewed)==1483 and len(a['other_active_reservations'])==50
assert not ids & (reviewed|set(a['other_active_reservations'])|{372627,372628,368940})
assert ids=={e['mathdb_id'] for e in json.loads((R/'queue.json').read_text())}
records=[]
for e in json.loads((C/'manifest.json').read_text())['files']:
 if not e['path'].startswith('corpus/'):continue
 for n,line in enumerate((C/e['path']).open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   r['corpus_ref']={'path':str(C/e['path']),'line':n};records.append(r)
assert len(records)==50
(L/'records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
(L/'assignment-check.json').write_text(json.dumps({'assigned':sorted(ids),'reviewed_count':len(reviewed),'active_other_count':50,'exactset':True,'disjoint':True},indent=2)+'\n')
for r in records:print('\nID',r['mathdb_id'],r['title'],'\nSOURCE',r['source_url'],'\n',r['statement'])
