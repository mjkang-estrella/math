import pathlib,json,hashlib,sys,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;F=P/'frozen';I=F/'root-mathdb-stack-review-intake-r527';N='sol-mathdb-ordinal-balls-preliminary-review-r526';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),str(p);assert h(b)==e['sha256'],str(p)
def write(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
def exact(root,m):
 names={e['path'] for e in m['files']};assert len(names)==len(m['files']);assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names
 for e in m['files']:check(root/e['path'],e)
def validate():
 for e in j(P/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 for fn,size,sha in [('review.md',16080,'fb1ac8f4b43655cce0b3788f4bfb9a0dcfabae86bdc5f97efce012201a16cbec'),('manifest.json',6903,'bf50d47cf024ed32ab2e7995792b7aaee4c8ea45fec5d99d2d8fc4524306ffc7'),('verification-receipt.txt',1810,'99a69f17c14bd193f6e4a6491f4b84fc8a38e010c92ce82209013799b02bbd39')]:check(F/N/fn,{'size':size,'sha256':sha})
 m=j(F/N/'manifest.json');exact(F/N,m);exact(L/N,m)
 for e in j(F/N/'flatbindings.json'):check(pathlib.Path(e['path']),e)
 exact(L/'root-mathdb-stack-review-intake-r527',j(I/'manifest.json'))
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4233
 return cov
def build():
 cov=validate();write('coverage-delta.json',cov)
 adj=j(I/'adjudications.json');adj['366370']={'disposition':'EXCLUDE_ROUTINE_SOURCE_RESTRICTION','credit':0,'math_status':'Independent reviewer ordinary PASS; not root replayed','review':N+'/review.md','source':'Keller–Petrov, Acta Math. Hungar.160(2020),119–152; DOI10.1007/s10474-019-00972-z; published online2019-09-05','complete_bridge':'Restrict Example6.2 table6.1 to {a,b,e,f}; relabel(f,e,a,b) as(0,1,2,3); increasing normalization of image ranks gives exact producer matrix and nine cut-balls. No distinctness or ordinal-axiom gap reported.','priority_limit':'Actual published relevant body/table inspected; no claim that a separately named refutation was printed; global prior and registry remain HOLD','process_limits':'Reviewer inadvertently displayed unrelated stack code without executing it; Figure2 image viewed before derivative hash. Both disclosed.'}
 write('adjudications.json',adj);hyp=j(I/'hypothesis-queue.json')
 for q in hyp:
  if q['mathdb_id']==366370:q['status']='EXCLUDE_ROUTINE_SOURCE_RESTRICTION';q['credit']=0;q['review']=N+'/review.md'
 write('hypothesis-queue.json',hyp)
 active=j(I/'active-breadth-reservations.json');assert len(active)==1;claude=active[0];claude['active_hypothesis_ids']=[365437,365439]
 blocked=set(map(int,cov))|set(claude['ids'])|set(claude['protected_ids'])
 route=[json.loads(l) for l in (I/'routing-queue.jsonl').open()];assert len(route)==6000
 (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes());rows=[r for r in route if r['mathdb_id'] not in blocked][:50];assert len(rows)==50
 res={'lane':'sol-mathdb-primary-qualified-breadth-r530','ids':[r['mathdb_id'] for r in rows],'coverage_baseline':4233,'protected_ids':sorted(set(claude['protected_ids'])|{366370}),'active_hypothesis_ids':[365437,365439],'other_active_reservations':claude['ids'],'status':'reserved_not_reviewed'}
 claude['other_active_reservations']=res['ids'];write('active-breadth-reservations.json',[claude,res]);write('queue.json',rows);write('reserved-ids.json',res)
 (P/'DECISION.md').write_text('''# Root r529: ordinal-ball credit exclusion

Adopt independent r526's complete source-restriction bridge and EXCLUDE366370 from discovery credit. Preserve the mathematically valid ordinary witness: nine distinct cut-balls on four points. It is exactly the source Example6.2 restriction to{a,b,e,f}, relabeled(f,e,a,b) and rank-normalized. Image restriction retains surjectivity; symmetry/zero separation/distinct positive unordered ranks and cut-ball exhaustiveness remain satisfied. The known metric lift earns no credit. No Lean/manuscript investment.

Chronology correction: actual published relevant body is ActaMathHungar160(2020),119–152, online2019-09-05; arXivv1uploaded2024is not first publication. Reviewer inspected published definitions,table6.1,Figure2/Conj6.3 and compared arXiv. Do not claim a separately printed named refutation or complete global priority clearance. Published EchelonedSpaces2025 relevant proofs obtained; metrizability is not a ball-count subsumer. Global prior/registry remains held without affecting this positive source-adaptation exclusion.

Preserve reviewer deviations: accidentally displayed stack scientific code (no execution/conclusion) and Figure2PNG viewed before derivative binding; later hashes do not cure timing. Independent mathematics is the reviewer's report; root executed only file/receipt/administrative checks, no mathematical checker or upstream verifier.

Coverage unchanged4,233 literal reviews; counts9additional/39total/next40. Sol r528 stack-fiber review continues. Return freed Sol slot to breadth r530 with fifty disjoint metadata-routed records. Claude r504 remains rate-limited with fifty unreviewed reserved IDs. No provider replacement or retry. Existing adjudications otherwise unchanged.
''')
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in {'manifest.json','verification-receipt.json'}:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':h(b),'size':len(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files})
def verify():
 cov=validate();assert j(P/'coverage-delta.json')==cov;active=j(P/'active-breadth-reservations.json');seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not set(map(str,ids))&set(cov) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==100
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 assert set(j(P/'reserved-ids.json')['ids'])=={r['mathdb_id'] for r in j(P/'queue.json')};assert (P/'routing-queue.jsonl').read_bytes()==(I/'routing-queue.jsonl').read_bytes()
 exact(P,j(P/'manifest.json'))
 try:check(P/'DECISION.md',{'size':0,'sha256':'0'*64})
 except AssertionError:pass
 else:raise AssertionError('negative accepted')
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','coverage_unchanged':4233,'child_payloads':44,'child_flat_references':len(j(F/N/'flatbindings.json')),'root_binding_pairs':len(j(P/'bindings.json')),'original_chunks':20,'frozen_inputs':8,'reservation_disjointness':True,'negative_rejection':True,'root_mathematical_replay':False,'counts':{'additional':9,'total':39,'next':40}};write('verification-receipt.json',r);print(json.dumps(r))
if '--build' in sys.argv:build();print('built')
else:verify()
