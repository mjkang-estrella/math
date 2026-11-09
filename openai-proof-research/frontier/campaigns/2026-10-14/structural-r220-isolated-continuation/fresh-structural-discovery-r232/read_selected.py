from pathlib import Path
import sys,json,hashlib,datetime
R=Path(__file__).parent
A=json.loads((R/'authentication-private.json').read_text())
for spec in sys.argv[1:]:
 fam,tail,start,end=spec.split(':'); prefix='Giglis-' if fam=='G' else 'Weak-Hessian-'
 matches=[x for x in A if x['path'].split('/')[1].startswith(prefix) and x['path'].endswith('/'+tail)]
 assert len(matches)==1, matches
 row=matches[0];b=(R/row['local']).read_bytes(); a=int(start);z=len(b) if end=='end' else int(end)
 assert 0<=a<=z<=len(b)
 boundaries={0,len(b)};n=0
 for l in b.splitlines(keepends=True):n+=len(l);boundaries.add(n)
 assert a in boundaries and z in boundaries,(a,z)
 print('\nEXACT SEMANTIC READ',fam,tail,f'[{a},{z})',hashlib.sha256(b[a:z]).hexdigest());print(b[a:z].decode())
 with (R/'semantic-reads-private.jsonl').open('a') as f:f.write(json.dumps({'file':row['local'],'start':a,'end':z,'sha256':hashlib.sha256(b[a:z]).hexdigest(),'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'parser':'bytes.splitlines(keepends=True)','truncation':'none unless separately recorded'})+'\n')
