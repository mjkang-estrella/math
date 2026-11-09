import pathlib,json,time
D=pathlib.Path(__file__).resolve().parents[1]
clauses={};n=0
for l in (D/'outputs/percolation-sym-5-5.cnf').read_text().splitlines():
 if l.startswith(('c','p')):continue
 n+=1;clauses[n]=list(map(int,l.split()[:-1]))
steps={};deletions=0;end=None;t=time.monotonic()
for l in (D/'outputs/percolation-5-5.lrat').read_text().splitlines():
 ss=l.split();i=int(ss[0])
 if ss[1]=='d':deletions+=1;continue
 vals=list(map(int,ss[1:]));j=vals.index(0);c=vals[:j];h=vals[j+1:-1];assert all(x>0 for x in h),'RAT unsupported'
 assignment={};contradiction=False
 for x in c:
  v=abs(x);b=x<0
  if v in assignment and assignment[v]!=b:contradiction=True
  assignment[v]=b
 for hint in h:
  if contradiction:break
  clause=clauses[hint];un=[];sat=False
  for x in clause:
   a=assignment.get(abs(x))
   if a is None:un.append(x)
   elif a==(x>0):sat=True;break
  assert not sat and len(un)<=1,('not a RUP propagation',i,hint)
  if not un:contradiction=True
  else:assignment[abs(un[0])]=un[0]>0
 assert contradiction,('no contradiction',i)
 clauses[i]=c;steps[i]=(c,h)
 if not c:end=i
assert end
needed=set();todo=[end]
while todo:
 i=todo.pop()
 if i in needed:continue
 needed.add(i)
 if i in steps:todo.extend(steps[i][1])
usedsteps=sorted(i for i in needed if i in steps);ren={i:i for i in range(1,n+1)};ren.update({i:n+1+j for j,i in enumerate(usedsteps)})
out=[]
for i in usedsteps:
 c,h=steps[i];out.append('%d %s0 %s0\n'%(ren[i],''.join(str(x)+' ' for x in c),''.join(str(ren[x])+' ' for x in h)))
(D/'outputs/percolation-5-5-trim.lrat').write_text(''.join(out))
r={'result':'All additions independently verified as RUP, ignoring deletions (safe monotone database)','input_clauses':n,'additions':len(steps),'ignored_deletions':deletions,'used_additions':len(usedsteps),'used_input_clauses':len([i for i in needed if i<=n]),'final_empty_id':end,'trim_final_empty_id':ren[end],'wall_seconds':time.monotonic()-t}
(D/'outputs/lrat-check.json').write_text(json.dumps(r,indent=2));print(r)
