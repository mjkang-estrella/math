import pathlib,json,hashlib,datetime,re,math
from fractions import Fraction as F
L=pathlib.Path(__file__).resolve().parent; I=L.parent/'root-mathdb-breadth-intake-r465'; V=L.parent/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def save(n,x):(L/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
def ids(x):
 out=set()
 if isinstance(x,dict):
  for k,v in x.items():
   if k in ['mathdb_id','related_mathdb_id'] and isinstance(v,int):out.add(v)
   elif k in ['mathdb_ids','problem_ids'] and isinstance(v,list):out.update(v)
   else:out.update(ids(v))
 elif isinstance(x,list):
  for v in x:out.update(ids(v))
 return out
r=load(I/'reserved-ids.json'); q=load(I/'queue.json'); cov=load(I/'coverage-delta.json'); assert len(cov)==3033,len(cov)
assigned=set(r['ids']); assert len(assigned)==50 and assigned=={x['mathdb_id'] for x in q}; assert r['lane']==L.name
ex=set([372627,372628,368940,404067,364119])|set(r['other_active_reservations'])|set(map(int,cov))
for p in [L.parent/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L.parent/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L.parent/'root-mathdb-cayley-review-intake-r363/disposition.json'] :ex.update(ids(load(p)))
assert not assigned&ex,assigned&ex
m=load(V/'manifest.json'); frozen=[]
for e in m['frozen_inputs']:
 p=V/e['path']; b=p.read_bytes(); assert sha(b)==e['sha256'] and len(b)==e['bytes'];frozen.append({'path':str(p),'bytes':len(b),'sha256':sha(b)})
save('inventory-frozen-inputs.json',frozen)
save('assignment-receipt.json',{'baseline_reported_reviews':len(cov),'assigned_count':50,'queue_exact_match':True,'all_exclusion_disjoint':True,'excluded_ids':sorted(ex),'other_active_reservations':r['other_active_reservations'],'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
# Small exact checks; no dependency or novelty claims.
for n in range(21):
 c=F(math.comb(2*n,n),4**n)
 for j in range(41):
  x=F(j,40); assert sum((math.comb(n,k)**2*x**(2*k)*(1-x)**(2*(n-k)) for k in range(n+1)),F(0))>=c
prime=[True]*10001;prime[0]=prime[1]=False
for p in range(2,101):
 if prime[p]:
  for j in range(p*p,10001,p):prime[j]=False
for n in range(12,10001,2):
 p=max(j for j in range(2,n) if prime[j]); assert any(prime[a] and prime[n-a] and a<n-a<p for a in range(2,n//2))
checks={'327182':{'status':'executed_exact_bounded','n':'0..20','x':'j/40, j=0..40','cases':861,'outcome':'no violation; known theorem, no proof credit'},'328448':{'status':'executed_exact_bounded','n':'all even 12..10000','cases':4995,'outcome':'no violation; no unbounded inference'}}
save('bounded-checks.json',checks)
notes={int(a):[b,c] for a,b,c in (v.split('\t',2) for v in (L/'assessment.tsv').read_text().splitlines())}; assert set(notes)==assigned
passages=load(L/'passage-locators.json'); versions={pathlib.Path(x['file']).stem:x['version_marks'] for x in passages}
records=load(L/'assigned-records.json'); out=[]
for a in records:
 x=a['record']; ident=x['mathdb_id']; src=x['source_url'].rsplit('/',1)[-1]; p=L/'sources'/(src+'.txt'); status,reason=notes[ident]
 out.append({'mathdb_id':ident,'literal_statement':x['statement'],'statement_utf8_sha256':sha(x['statement'].encode()),'canonical_record_sha256':sha(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()),'original_chunk':str(V/a['chunk']),'original_line_1based':a['line'],'canonical_url':x['canonical_url'],'source_url':x['source_url'],'disposition':status,'full_scope_mechanism_or_obstacle':reason,'source_level':'primary selected passages read; see passage-locators.json (splitlines numbering) and assessment; no whole-body claim' if p.exists() else 'corpus literal only; primary retrieval 404 HOLD','source_version':versions.get(src,[]),'source_scope_cleared':False,'whole_body_read':False,'proof_level':'public theorem/refutation statement match; no complete proof dependency audit' if status.startswith('EXCLUDE') else 'no full-scope proof or counterexample established','proof_dependency_audit':'not_complete','registry_level':'HOLD: zero MathDB requests, inherited 429. AIM/Kourovka/EGRES, AIProofWatch and denied routes remain parked; current registry head not cleared.','successor_level':'selected primary successor theorem read' if ident in [327182,328500,329073] else 'revised source inspected; closest later successors not comprehensively cleared; HOLD','bounded_check':checks.get(str(ident),{'status':'not_run','reason':'No small complete certificate route established; metadata or passage matching is not a mathematical bounded check.'}),'accepted_credit':0,'prior_cleared':False})
save('dispositions.json',sorted(out,key=lambda x:x['mathdb_id']));save('proposals.json',[])
# Retain exact source receipt, version and text hashes without rewriting fetch logs.
receipts=load(L/'source-receipts.json')+load(L/'successor-receipts.json')
for e in receipts:
 if 'file' in e:
  p=L/e['file'];text=p.with_suffix('.txt');s=text.read_text();e['version_read']=re.findall(r'arXiv:\S+',s)[:1];e['text_file']=str(text.relative_to(L));e['text_sha256']=sha(text.read_bytes())
save('retained-sources.json',receipts)
print('PASS 50 assigned, baseline3033, exclusions/disjointness; 861 Bernstein cases; 4995 Goldbach cases; proposals0')
