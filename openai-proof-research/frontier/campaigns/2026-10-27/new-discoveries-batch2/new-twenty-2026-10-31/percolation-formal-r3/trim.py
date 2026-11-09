from pathlib import Path
import sys,json,time
r=Path(__file__).resolve().parent; name=sys.argv[1]; t=time.monotonic()
clauses={}
for line in (r/(name+'.cnf')).open():
 if line[0] in 'cp':continue
 clauses[len(clauses)+1]=list(map(int,line.split()))[:-1]
n=len(clauses); adds={};end=None
for line in (r/(name+'.lrat')).open():
 w=line.split()
 if len(w)<2 or w[1]=='d':continue
 row=list(map(int,w)); i=row.index(0,1); c=row[1:i];h=row[i+1:-1]
 adds[row[0]]=(c,h)
 if not c:end=row[0]
assert end is not None
needed=set();stack=[end]
while stack:
 i=stack.pop()
 if i in needed:continue
 needed.add(i)
 if i>n:
  assert i in adds
  assert all(h>0 and h<i for h in adds[i][1])
  stack.extend(adds[i][1])
rows=[]; maxh=0
for i,(c,hs) in adds.items():
 if i not in needed:continue
 false=set(c);conflict=False
 for h in hs:
  d=clauses[h];rem=[z for z in d if z not in false]
  if not rem:conflict=True;break
  assert len(rem)==1,(i,h,rem)
  false.add(-rem[0])
 assert conflict,i
 clauses[i]=c;rows.append([i,c,hs]);maxh=max(maxh,len(hs))
(r/(name+'-trimmed.json')).write_text(json.dumps({'inputs':n,'used_inputs':sorted(i for i in needed if i<=n),'steps':rows}))
res={'additions':len(rows),'used_inputs':sum(i<=n for i in needed),'last_id':end,'max_hints':maxh,'seconds':time.monotonic()-t}
(r/(name+'-trim-results.json')).write_text(json.dumps(res,indent=2));print(res)
