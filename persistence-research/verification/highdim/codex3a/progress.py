import sys
sys.dont_write_bytecode=True
import json,collections,re,math
from pathlib import Path
HERE=Path(__file__).resolve().parent
h=[json.loads(l) for l in open(HERE/'history.jsonl')]
r={32:{},14112:{}}
for x in h:
    t=x['target'];k=x['key']
    if x['result']['status']=='CLOSED' or r[t].get(k,{}).get('status')!='CLOSED':r[t][k]=x['result']
for t in r:print(t,'attempted',len(r[t]),dict(collections.Counter(v['status'] for v in r[t].values())))
rank={}
for x in h:
    v=x['result'];b=v['budget'];f=v['far'];reason=v.get('stop_reason') or ''
    if x['target']!=14112 or len(f)!=4 or b.get('profile')!='early2':continue
    m=re.search(r'level needs (\d+) lifts',reason)
    if not m:continue
    cost=int(m.group(1))+v['lifts_attempted'];sym=math.prod(math.factorial(n) for n in collections.Counter(f).values())
    rank[x['key']]=(cost/sym,cost,sym)
print('easiest failed final levels',sorted(rank.items(),key=lambda kv:kv[1])[:20])
