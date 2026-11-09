import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;C=P.parent/'pi-mathdb-full-corpus-inventory-r301'
m=json.loads((P/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_text())
entries=[e for e in m['files'] if e['path'].endswith('screening-tags.jsonl')];assert len(entries)==1
e=entries[0];src=C/e['path'];b=src.read_bytes();assert len(b)==e.get('size',e.get('bytes')) and hashlib.sha256(b).hexdigest()==e['sha256']
rows=json.loads((P/'bindings.json').read_text());assert str(src) not in [x['original'] for x in rows]
rows.append({'original':str(src),'copy':str(src),'sha256':e['sha256'],'size':len(b),'mode':'immutable_in_place_no_copy'})
(P/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n');print('tags bound in place',len(b),e['path'])
