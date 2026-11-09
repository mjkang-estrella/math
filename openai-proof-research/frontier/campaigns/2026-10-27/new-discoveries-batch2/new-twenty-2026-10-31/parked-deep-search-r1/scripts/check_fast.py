# Independent stamped-array RUP checker, accepts positive LRAT only.
# Streams a trimmed proof; each chunk imports previously checked clauses but checks
# only the requested addition range. A full certificate needs ALL chunk reports.
import sys,pathlib,json,time
D=pathlib.Path(sys.argv[1]);stem=sys.argv[2];lo=int(sys.argv[3]);hi=int(sys.argv[4]);p=D/'outputs'/stem;db={};mx=0
for line in p.with_suffix('.cnf').open():
 if line.startswith(('c','p')):continue
 c=list(map(int,line.split()))[:-1];db[len(db)+1]=c;mx=max(mx,max(map(abs,c),default=0))
stamp=[0]*(mx+1);value=[False]*(mx+1);serial=0;checked=0;last=None;num=0
for line in p.with_suffix('.lrat').open():
 a=line.split()
 if not a or a[1]=='d':continue
 num+=1
 if num>hi:break
 a=list(map(int,a));z=a.index(0);i=a[0];c=a[1:z];last=c
 if num>=lo:
  serial+=1
  for x in c:stamp[abs(x)]=serial;value[abs(x)]=x<0
  conflict=False
  for h in a[z+1:-1]:
   assert h>0 and h in db and h<i
   free=0;unit=0;sat=False
   for x in db[h]:
    v=abs(x)
    if stamp[v]!=serial:free+=1;unit=x
    elif value[v]==(x>0):sat=True;break
   assert not sat
   if free==0:conflict=True;break
   assert free==1,(i,h,free)
   v=abs(unit);stamp[v]=serial;value[v]=unit>0
  assert conflict,i
  checked+=1
 db[i]=c
r=dict(stem=stem,first=lo,last=min(num,hi),checked=checked,last_clause_empty=last==[])
(D/'outputs'/f'{stem}.chunk-{lo}-{hi}.json').write_text(json.dumps(r));print(r)
