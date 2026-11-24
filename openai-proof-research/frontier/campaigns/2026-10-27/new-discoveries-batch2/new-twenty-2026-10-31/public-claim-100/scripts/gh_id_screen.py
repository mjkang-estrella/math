#!/usr/bin/env python3
"""Root screen: GitHub code/repo search for each accepted MathDB id (public solutions keyed by id)."""
import json,subprocess,time,sys,os
C=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ids=[r['mathdb_id'] for r in json.load(open(os.path.join(C,'base-rows.json')))]+[339461,366210,358938]
out_p=os.path.join(C,'gh-id-screen.json')
out=json.load(open(out_p)) if os.path.exists(out_p) else {}
def run(args):
    for attempt in range(4):
        r=subprocess.run(['gh']+args,capture_output=True,text=True)
        if r.returncode==0:
            try: return json.loads(r.stdout or '[]')
            except Exception: return []
        if 'rate limit' in r.stderr.lower() or '403' in r.stderr or '429' in r.stderr: time.sleep(65); continue
        return {'error':r.stderr[:200]}
    return {'error':'rate limited'}
for i in ids:
    k=str(i)
    if k in out: continue
    res={}
    for q in (f'mathdb-{i}', f'"MathDB {i}"', f'mathdb.com/p/{i}'):
        v=run(['search','code',q,'--limit','30','--json','repository,path'])
        res[q]=[f"{x['repository']['nameWithOwner']}:{x['path']}" for x in v] if isinstance(v,list) else v
        time.sleep(7)
    v=run(['search','repos',f'mathdb {i}','--limit','20','--json','fullName,createdAt,description'])
    res['repos']=[f"{x['fullName']} {x['createdAt']}" for x in v] if isinstance(v,list) else v
    time.sleep(3)
    out[k]=res
    json.dump(out,open(out_p,'w'),indent=1)
print('done',len(out))
