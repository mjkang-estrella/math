import pathlib,json,hashlib,time,sys
L=pathlib.Path.cwd();cnf=pathlib.Path(sys.argv[1]);proof=pathlib.Path(sys.argv[2]);db={};nvars=0
for line in cnf.open():
 if line.startswith('p'):nvars=int(line.split()[2])
 elif line and line[0] not in 'cp%\n':
  cl=list(map(int,line.split()));assert cl[-1]==0; db[len(db)+1]=cl[:-1]
input_count=len(db);last=input_count;count=0;empty=False;start=time.monotonic()
for lineno,line in enumerate(proof.open(),1):
 ts=line.split()
 if not ts:continue
 ident=int(ts[0])
 if ts[1]=='d':continue # retaining clauses preserves soundness
 assert ident>last,(lineno,ident,last)
 ns=list(map(int,ts[1:]));end=ns.index(0);cl=ns[:end];hints=ns[end+1:];assert hints[-1]==0
 assigned={};taut=False
 for lit in cl:
  assert 0<abs(lit)<=nvars
  v=abs(lit);val=lit<0
  if v in assigned and assigned[v]!=val:taut=True;break
  assigned[v]=val
 conflict=taut
 if not taut:
  for h in hints[:-1]:
   assert h>0 and h in db,(lineno,'not positive RUP hint',h)
   pending=[];sat=False
   for lit in db[h]:
    v=abs(lit)
    if v not in assigned:pending.append(lit)
    elif assigned[v]==(lit>0):sat=True;break
   assert not sat,(lineno,'satisfied hint',h)
   pending=list(set(pending))
   if not pending:conflict=True;break
   assert len(pending)==1,(lineno,'not unit',h,pending)
   lit=pending[0];assigned[abs(lit)]=lit>0
 assert conflict,(lineno,'no conflict')
 db[ident]=cl;last=ident;count+=1
 if not cl:empty=True
assert empty and db[last]==[]
result=dict(input_clauses=input_count,additions=count,final_id=last,seconds=time.monotonic()-start,cnf_sha256=hashlib.sha256(cnf.read_bytes()).hexdigest(),proof_sha256=hashlib.sha256(proof.read_bytes()).hexdigest())
(L/(sys.argv[3]+'.json')).write_text(json.dumps(result,indent=2));print(result)
