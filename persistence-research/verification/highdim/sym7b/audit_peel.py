#!/usr/bin/env python3
"""Independent certificate containment and exhaustive position-split audit.
No search/generator/arithmetic-checker imports. Only stdlib and copied finite scan.
"""
import sys
sys.dont_write_bytecode=True
import collections,hashlib,itertools,json,math,pathlib
H=pathlib.Path(__file__).resolve().parent;R=H.parents[2]
sys.path.insert(0,str(H))
from audit_coverage import finite_scan

def load(p):return json.loads(pathlib.Path(p).read_text())
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def save(p,v):
 t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(v,indent=1)+'\n');t.replace(p)
def sid(K,cs,p):return str(K)+':'+','.join(map(str,cs))+':'+str(p)
def v2(K):return (K&-K).bit_length()-1

def controls():
 # Independent direct tuple enumeration vs routing through exact group decisions.
 cases=points=0;edge=collections.Counter()
 for cs in ((9,9),(9,18),(9,9,18),(18,54,72),()):
  for K in (8,89,188,1844,5408):
   for L in range(3,10):
    seen=set()
    for qs in itertools.permutations(range(3,L),len(cs)):
     point=tuple((c,tuple(sorted(q for d,q in zip(cs,qs) if d==c))) for c in sorted(set(cs)))
     if point in seen:continue
     seen.add(point);constant=K;remaining=list(cs);p=3;fixed=[]
     # Synthetic stopping rule includes occupancy, empty steps and v2 changes.
     while p<min(L,7):
      occupants=[c for c,q in zip(cs,qs) if q==p]
      assert len(occupants)<=1
      if occupants:
       c=occupants[0];remaining.remove(c);constant+=c*10**p;fixed.append(p)
       edge['occupied']+=1
      else:edge['empty']+=1
      edge['v2_changed']+=v2(constant)!=v2(K)
      p+=1
     free=[(c,q) for c,q in zip(cs,qs) if q>=p]
     assert sorted(remaining)==sorted(c for c,q in free)
     assert all(q<L and q>=p for c,q in free)
     assert len(fixed)==len(set(fixed))
     assert constant+sum(c*10**q for c,q in free)==K+sum(c*10**q for c,q in zip(cs,qs))
     X=10**L+constant+sum(c*10**q for c,q in free)
     if p>v2(constant):
      t=v2(constant);assert v2(X)==t
      D=5**p*2**max(p-t,0)
      assert (X//2**t-constant//2**t)%D==0
      edge['deepest_legal_pin']+=1
     else:edge['floor_requires_further_peeling']+=1
     points+=1
    cases+=1
 return {'result':'PASS','cases':cases,'canonical_points':points,'events':dict(edge)}

def main():
 assignment=load(H/'assignment.json')['configurations'];tree=load(H/'tree.json');states=tree['states'];checks=load(H/'checks.json') if (H/'checks.json').exists() else {}
 checker_paths={'M':R/'verification/highdim/sym5/check_sym5.py','F5':R/'verification/indep5/check_sym_F5.py'}
 assert set(assignment)==set(tree['roots'])
 assert load(H.parent/'sym6/summary.json')['open']==list(assignment)
 assert sha(H.parent/'sym6/summary.json')==load(H/'assignment.json')['source_sha256']
 original=load(H.parent/'sym6/assignment.json')['configurations']
 assert all(rec==original[key] for key,rec in assignment.items())
 # All states, even those not used by a completed cover, must have valid splits.
 splits=0;files=set();B=3;invalid=[]
 for i,s in states.items():
  K,cs,p=s['K'],tuple(s['coefs']),s['p'];B=max(B,p)
  assert i==sid(K,cs,p) and list(cs)==sorted(cs) and K>0
  if s['status']=='SPLIT':
   expected={'empty':sid(K,cs,p+1)}
   for c in sorted(set(cs)):
    rest=list(cs);rest.remove(c);expected[str(c)]=sid(K+c*10**p,rest,p+1)
   assert s['children']==expected,(i,'nonexhaustive/false split')
   assert all(ch in states for ch in expected.values());splits+=1
  elif s['status']=='CERTIFICATE':
   f=s['file'];files.add(f)
   with open(f) as stream:m=json.loads(next(stream))
   assert sha(f)==s['sha256'];assert m['scope']=='full'
   assert m['K']==K and tuple(c for c,n in m['groups'] for _ in range(n))==cs
   assert m['qmin']<=p and m['qmin']>v2(K)
   assert 0<=m['pin_digits']<=m['qmin']
   if m.get('pin2'):assert m['qmin']>=v2(K)+3
   for who,checker in checker_paths.items():
    c=checks.get(f,{}).get(who,{})
    if not (c.get('result')=='PASS' and c.get('sha256')==sha(f) and c.get('checker_sha256')==sha(checker)):
     invalid.append({'state':i,'file':f,'checker':who})
   pair=checks.get(f,{})
   if all(pair.get(w,{}).get('result')=='PASS' for w in checker_paths):
    assert sorted(pair['M']['check']['solutions'])==sorted(pair['F5']['check']['claimed']),'checker solution disagreement'
  else:assert s['status'] in ('PENDING','OPEN')
 allvisited=set();results={};allsolutions=[]
 for key,rec in assignment.items():
  root=tree['roots'][key];assert root==sid(9*rec['S_low']-1,tuple(sorted(rec['far'])),3)
  todo=[root];seen=set();used=set();missing=[]
  while todo:
   i=todo.pop()
   if i in seen:continue
   seen.add(i);s=states[i]
   if s['status']=='SPLIT':todo.extend(s['children'].values())
   elif s['status']=='CERTIFICATE':used.add(s['file'])
   else:missing.append(i)
  allvisited.update(seen)
  unchecked=[v for v in invalid if v['state'] in seen]
  results[key]={'k':len(rec['far']),'states':len(seen),'certificates':len(used),'domains':sorted(used),'unresolved':sorted(missing),'unchecked':unchecked,'status':'CLOSED' if not missing and not unchecked else 'OPEN'}
  # Every solution of an enlarged terminal domain is filtered back to the original.
  for f in used:
   ch=checks.get(f,{}).get('M',{}).get('check',{})
   with open(f) as stream:m=json.loads(next(stream))
   cs=[c for c,n in m['groups'] for _ in range(n)]
   for pt in ch.get('solutions',[]):
    X=10**pt[0]+m['K']+sum(c*10**q for c,q in zip(cs,pt[1:]));assert X%9==0
    n=X//9;ds=str(n);low=sum((int(d)-1)*10**i for i,d in enumerate(ds[::-1][:3]));far=sorted(9*(int(d)-1) for d in ds[::-1][3:] if d!='1')
    if str(low)+'|'+','.join(map(str,far))==rec['key'] and math.prod(map(int,ds))==rec['target']:allsolutions.append({'configuration':key,'n':n,'source':f})
 assert allvisited==set(states),'unreachable proof states'
 finite=finite_scan(B,{111132:{rec['key']:rec for rec in assignment.values()}})
 for r in finite['members']:allsolutions.append({'configuration':str(r['target'])+':'+r['key'],'n':r['member'],'source':'finite_scan'})
 for m in allsolutions:results[m['configuration']]['status']='MEMBER_FOUND'
 counts={str(k):{'assigned':sum(v['k']==k for v in results.values()),'closed':sum(v['k']==k and v['status']=='CLOSED' for v in results.values()),'open':sum(v['k']==k and v['status']!='CLOSED' for v in results.values())} for k in (6,7,8)}
 out={'split_result':'PASS','coverage_result':'COMPLETE' if all(v['status']=='CLOSED' for v in results.values()) else 'INCOMPLETE','split_nodes':splits,'state_count':len(states),'certificate_files':len(files),'unchecked_references':invalid,'finite':finite,'members':allsolutions,'counts_by_k':counts,'configurations':results,'controls':controls()}
 save(H/'coverage_audit.json',out);save(H/'summary.json',{'counts_by_k':counts,'closed':[k for k,v in results.items() if v['status']=='CLOSED'],'open':[k for k,v in results.items() if v['status']!='CLOSED'],'coverage_result':out['coverage_result'],'split_result':'PASS','configurations':results})
 # Ledger every certificate, including partial-configuration successes.
 kills={};total=collections.Counter();witnesses=collections.Counter()
 for f in sorted((H/'certs').glob('*.jsonl')):
  with f.open() as stream:m=json.loads(next(stream));nodes=[json.loads(line) for line in stream if line.strip()]
  refs=collections.Counter();dep=set()
  for n in nodes:
   primes=n.get('rest',[])+([n['x']['prime']] if n.get('k')=='l' and 'prime' in n.get('x',{}) else [])
   refs['prime_witness_references']+=len(primes)
   if n.get('k')=='l' and 'sz' in n.get('x',{}):refs['size_leaves']+=1;dep.add('size')
   if primes:
    dep.add('prime_coset')
    if m.get('pin_digits'):dep.add('decimal_tail_coset')
    if m.get('pin2'):dep.add('mod8_parity')
    for prime in primes:
     if n.get('m2',n['m'])%_order10(prime):refs['unaligned_sumset_references']+=1;dep.add('unaligned_sumset')
  total.update(dep);witnesses.update(refs)
  kills[str(f)]={'sha256':sha(f),'meta':m,'dependency_types':sorted(dep),'references':dict(refs),'checks':{w:checks.get(str(f),{}).get(w,{}).get('result','PENDING') for w in checker_paths}}
 save(H/'kill_usage.json',{'files':kills,'dependency_totals':dict(total),'witness_totals':dict(witnesses),'withdrawn_candidates':load(H/'withdrawn.json') if (H/'withdrawn.json').exists() else []})
 print(json.dumps({k:out[k] for k in ('split_result','coverage_result','split_nodes','state_count','certificate_files','counts_by_k','finite','controls')}))

_order_hints={p:d for p,d,a,w in load(H/'supply.json')}
_order_cache={}
def _order10(p):
 if p not in _order_cache:
  d=_order_hints.get(p,p-1)
  if pow(10,d,p)!=1:d=p-1
  remaining=d;factor=2
  while factor*factor<=remaining:
   if remaining%factor==0:
    while remaining%factor==0:remaining//=factor
    while d%factor==0 and pow(10,d//factor,p)==1:d//=factor
   factor+=1
  if remaining>1:
   while d%remaining==0 and pow(10,d//remaining,p)==1:d//=remaining
  assert pow(10,d,p)==1
  _order_cache[p]=d
 return _order_cache[p]
if __name__=='__main__':main()
