"""Independent peeling cover auditor: no search/generator/checker imports."""
import sys
sys.dont_write_bytecode=True
import collections,hashlib,itertools,json,math,pathlib
H=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(H))
from audit_coverage import finite_scan

def read(p):return json.loads(pathlib.Path(p).read_text())
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def save(p,o):
 t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(o,indent=1)+'\n');t.replace(p)
def key(K,cs,p):return '%d:%s:%d'%(K,','.join(map(str,cs)),p)
def v2(K):return (K&-K).bit_length()-1

def controls():
 cases=points=0
 for cs in ((9,9),(9,18),(9,9,18),(18,27,54)):
  for initial in (8,98,5606):
   for L in range(3,10):
    expected=set()
    for qs in itertools.permutations(range(3,L),len(cs)):
     expected.add(tuple((c,tuple(sorted(q for d,q in zip(cs,qs) if d==c))) for c in sorted(set(cs))))
    actual=set();todo=[(initial,tuple(sorted(cs)),3,())]
    while todo:
     K,rest,p,fixed=todo.pop()
     # Constant-dependent target tests t0 changes; p=5..7 forces raised floors.
     floor=5+v2(K)%3
     if p>=floor:
      local=set()
      for qs in itertools.permutations(range(p,L),len(rest)):
       assignment=fixed+tuple(zip(rest,qs))
       if any(q>=L for c,q in assignment):continue
       assert initial+sum(c*10**q for c,q in assignment)==K+sum(c*10**q for c,q in zip(rest,qs))
       pt=tuple((c,tuple(sorted(q for d,q in assignment if d==c))) for c in sorted(set(cs)))
       local.add(pt)
      assert not actual&local;actual|=local;continue
     todo.append((K,rest,p+1,fixed))
     for c in set(rest):
      r=list(rest);r.remove(c);todo.append((K+c*10**p,tuple(r),p+1,fixed+((c,p),)))
    assert expected==actual
    cases+=1;points+=len(expected)
 return {'result':'PASS','cases':cases,'canonical_points':points,'unique_exhaustive_assignment':True}

def main():
 assignment=read(H/'assignment.json');assert sha(assignment['source'])==assignment['source_sha256'];jobs=assignment['configurations']
 checks=read(H/'dual_checks.json') if (H/'dual_checks.json').exists() else {};valid={};ledger={}
 supply={r[0]:r[1:] for r in read(H/'supply.json')}
 for f,records in checks.items():
  digest=sha(f);meta=json.loads(pathlib.Path(f).open().readline());cs=tuple(c for c,n in meta['groups'] for _ in range(n))
  good=True
  for w in ('M','F5'):
   r=records.get(w,{})
   if r.get('result')!='PASS':good=False;continue
   if r['sha256']!=digest or r['checker_sha256']!=sha(r['command'][4]):good=False
  if good:
   assert sorted(records['M']['check']['solutions'])==sorted(records['F5']['check']['claimed'])
   assert meta['scope']=='full' and meta['root']=={'r':[0]+[[0]*n for c,n in meta['groups']],'m':1}
   assert meta['qmin']>v2(meta['K']) and 0<=meta['pin_digits']<=meta['qmin']
   valid[f]=(meta,cs,records['M']['check']['solutions'])
  counts=collections.Counter();witnesses=collections.Counter();sol=0
  with pathlib.Path(f).open() as stream:
   next(stream)
   for line in stream:
    nd=json.loads(line)
    if nd['k']=='i':
     for p in nd['rest']:
      counts['rest_references']+=1;witnesses[str(p)]+=1
    elif 'prime' in nd['x']:
     p=nd['x']['prime'];d=supply.get(p,[None])[0];counts['aligned_prime_leaves' if d and nd['m']%d==0 else 'sumset_prime_leaves']+=1;witnesses[str(p)]+=1
    else:counts['exact_size_leaves']+=1;sol+=len(nd['x']['sol'])
  ledger[f]={'sha256':digest,'K':meta['K'],'qmin':meta['qmin'],'t0':v2(meta['K']),'pin_digits':meta['pin_digits'],'pin2':meta['pin2'],'groups':meta['groups'],'dual_checked':good,'kills':dict(counts),'primes':{p:{'references':n,'supply_orders':supply.get(int(p))} for p,n in witnesses.items()},'declared_solutions':sol}
 results={};tree_audits=[];bound=2
 for path in sorted(H.glob('tree_*.json')):
  tree=read(path);name=tree['name'];rec=jobs[name];nodes=tree['nodes'];root=key(9*rec['S_low']-1,sorted(rec['far']),3)
  seen=set();todo=[root];used=set();missing=[];localbound=2;splits=0
  while todo:
   k=todo.pop()
   if k in seen:continue
   seen.add(k);n=nodes[k];K=n['K'];cs=n['coefs'];p=n['qmin']
   assert k==key(K,cs,p) and cs==sorted(cs) and n['t0']==v2(K)
   localbound=max(localbound,p-1)
   if n['kind']=='peel':
    expected=[key(K,cs,p+1)]
    for c in sorted(set(cs)):
     rest=list(cs);rest.remove(c);expected.append(key(K+c*10**p,rest,p+1))
    assert len(expected)==len(n['children']) and set(expected)==set(n['children'])
    assert set(n['order'])==set(cs) and len(n['order'])==len(set(cs))
    todo.extend(expected);splits+=1
   elif n['kind']=='certificate':
    f=n['file'];used.add(f)
    if f not in valid:missing.append({'state':k,'reason':'not dual checked','file':f});continue
    m,coeffs,sol=valid[f];assert m['K']==K and coeffs==tuple(cs) and m['qmin']<=p
   else:
    assert n['kind']=='open';missing.append({'state':k,'reason':n.get('reason','search incomplete')})
  assert seen==set(nodes),'unreachable cover states'
  assert used==set(tree['used'])
  audit={'tree':str(path),'sha256':sha(path),'name':name,'result':'PASS','exhaustive_partition':True,'states':len(seen),'peeling_splits':splits,'unresolved_leaves':len(missing),'missing':missing,'domains':sorted(used),'finite_Lmax':localbound,'status':'COVERED' if not missing else 'OPEN'}
  tree_audits.append(audit);bound=max(bound,localbound)
  old=results.get(name)
  if old is None or (audit['status']=='COVERED',-len(missing))>(old['status']=='COVERED',-old['unresolved_leaves']):results[name]=audit
 assert set(results)==set(jobs),'not all assigned configurations attempted'
 finite=finite_scan(bound,{14112:{r['key']:r for r in jobs.values()}})
 for name,row in results.items():
  rec=jobs[name];members={v['member'] for v in finite['members'] if v['key']==rec['key']}
  if row['status']=='COVERED':
   for f in row['domains']:
    m,cs,sol=valid[f]
    for pt in sol:
     X=10**pt[0]+m['K']+sum(c*10**q for c,q in zip(cs,pt[1:]));assert X%9==0
     n=X//9;ds=str(n);low=sum((int(d)-1)*10**i for i,d in enumerate(ds[::-1][:3]));far=sorted(9*(int(d)-1) for d in ds[::-1][3:] if d!='1')
     if math.prod(map(int,ds))==14112 and low==rec['S_low'] and far==rec['far']:members.add(n)
  row['members']=sorted(members);row['status']='CLOSED' if row['status']=='COVERED' and not members else 'OPEN';row['dim']=len(rec['far'])+1
 counts={str(d):{'assigned':sum(len(r['far'])+1==d for r in jobs.values()),'closed':sum(v['dim']==d and v['status']=='CLOSED' for v in results.values()),'open':sum(v['dim']==d and v['status']=='OPEN' for v in results.values())} for d in (6,7,8,9)}
 output={'label':'COMPUTED','counts_by_dimension':counts,'closed':sorted(k for k,r in results.items() if r['status']=='CLOSED'),'open':sorted(k for k,r in results.items() if r['status']=='OPEN'),'configurations':results,'checker_counts':{w:dict(collections.Counter(r[w]['result'] for r in checks.values() if w in r)) for w in ('M','F5')},'all_certificates_dual_checked':set(ledger)==set(valid) and all(str(p) in valid for p in (H/'certs').glob('*.jsonl')) and all(f in valid for t in tree_audits for f in t['domains']),'finite_scan':finite,'coverage_result':'PASS (exhaustive partitions; unresolved leaves remain OPEN)' if any(v['status']=='OPEN' for v in results.values()) else 'PASS (all complete covers)','controls':controls()}
 save(H/'kill_ledger.json',ledger);save(H/'coverage_audit.json',{'result':'PASS','auditor_sha256':sha(__file__),'trees':tree_audits,'controls':output['controls'],'finite_scan':finite});save(H/'summary.json',output)
 print(json.dumps({k:v for k,v in output.items() if k not in ('configurations','open','closed')}))
if __name__=='__main__':main()
