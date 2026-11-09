from pathlib import Path
import sys,json,time
r=Path(__file__).resolve().parent; name=sys.argv[1];t=time.monotonic()
with (r/(name+'.cnf')).open() as f:n=int(next(f).split()[3])
adds={};end=None
for line in (r/(name+'.lrat')).open():
 w=line.split()
 if len(w)<2 or w[1]=='d':continue
 row=list(map(int,w));i=row.index(0,1)
 adds[row[0]]=(row[1:i],row[i+1:-1])
 if i==1:end=row[0]
assert end is not None
needed=set();stack=[end]
while stack:
 i=stack.pop()
 if i in needed:continue
 needed.add(i)
 if i>n:
  assert i in adds and all(0<h<i for h in adds[i][1]);stack.extend(adds[i][1])
with (r/(name+'-trimmed.jsonl')).open('w') as f:
 f.write(json.dumps({'inputs':n,'used_inputs':sorted(i for i in needed if i<=n)})+'\n')
 for i,(c,h) in adds.items():
  if i in needed:f.write(json.dumps([i,c,h])+'\n')
res={'additions':sum(i>n for i in needed),'used_inputs':sum(i<=n for i in needed),'last_id':end,'seconds':time.monotonic()-t,'independent_check':'pending bounded shards'}
(r/(name+'-trim-results.json')).write_text(json.dumps(res,indent=2));print(res)
