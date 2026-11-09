from pathlib import Path
import sys,json,hashlib
p=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r155/packet/private'); rows=json.loads((p/'selected-tree.json').read_text())
families=list(dict.fromkeys(e['path'].split('/')[1] for e in rows))
fam=int(sys.argv[1]); term=sys.argv[2]
m=[e for e in rows if e['path'].split('/')[1]==families[fam] and (Path(e['path']).name==term or '/sections/'+term in e['path'])]; assert len(m)==1,m
s=m[0]['path']; b=(p/'upstream'/s).read_bytes(); start=int(sys.argv[3]) if len(sys.argv)>3 else 0; end=int(sys.argv[4]) if len(sys.argv)>4 else len(b); z=b[start:end]
print('FILE',s,'BYTE RANGE',start,end,'TOTAL',len(b)); print(z.decode())
with (p/'display-extents.jsonl').open('a') as f: f.write(json.dumps({'path':s,'start':start,'end':end,'sha256_slice':hashlib.sha256(z).hexdigest()})+'\n')
