import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r519/verify.py').read_text()
s=s.replace("I=F/'root-mathdb-breadth-intake-r517'","I=F/'root-mathdb-breadth-intake-r519'")
a=s.index('SPEC=');b=s.index('\ndef j(',a)
s=s[:a]+"SPEC=[('sol-mathdb-primary-qualified-breadth-r520',5455,'f4c909bbfb12a0e7244327c78601ed93280c05589c6992ad7c8f034d00b09b65','root-mathdb-breadth-intake-r519/reserved-ids-r520.json','corpus_chunk','corpus_line','statement_utf8_sha256')]"+s[b:]
s=s.replace("exact(L/'root-mathdb-breadth-intake-r517',j(I/'manifest.json'))","exact(L/'root-mathdb-breadth-intake-r519',j(I/'manifest.json'))")
s=s.replace('len(cov)==4083','len(cov)==4133').replace('len(cov)==3983','len(cov)==4083').replace('len(found)==100','len(found)==50')
s=s.replace("for e in j(F/name/'flat-bindings.json'):check(pathlib.Path(e['path']),e)","for path,e in j(F/name/'flat-bindings.json').items():check(pathlib.Path(path),e)")
a=s.index(" claude=next(");b=s.index(" (P/'DECISION.md').write_text(",a)
s=s[:a]+''' active=[r for r in j(I/'active-breadth-reservations.json') if r['lane']!='sol-mathdb-primary-qualified-breadth-r520']
 blocked=set(map(int,cov))|{i for r in active for i in r['ids']}|set(active[0]['protected_ids'])
 route=[json.loads(l) for l in (I/'routing-queue.jsonl').open()];assert len(route)==6000
 (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes())
 rows=[r for r in route if r['mathdb_id'] not in blocked][:50];assert len(rows)==50
 res={'lane':'sol-mathdb-primary-qualified-breadth-r524','ids':[r['mathdb_id'] for r in rows],'coverage_baseline':4133,'protected_ids':active[0]['protected_ids'],'active_hypothesis_ids':[],'status':'reserved_not_reviewed'}
 active.append(res);allids={i for r in active for i in r['ids']};assert len(allids)==150
 for r in active:r['other_active_reservations']=sorted(allids-set(r['ids']))
 write('queue.json',rows);write('reserved-ids.json',res);write('active-breadth-reservations.json',active)
'''+s[b:]
a=s.index(" (P/'DECISION.md').write_text(");b=s.index(' files=[]',a)
s=s[:a]+" (P/'DECISION.md').write_text("+repr('''# Root r523 reconciliation

Reconcile r520: fifty new disjoint literal reviews,48HOLDs,two eligibility exclusions,zero proposals. Latest reported literal coverage4,133; no full technical/novelty corpus claim. 363215 is wording-only;364336 source Theorem2.3 covers full Delta>=3,m<=4Delta-3 range, selected local proof only.363572 public theorem claim remains proof-unaudited.364319 source factorial averaging already covers its characteristic range, small-characteristic gap survives.363983 source-version alignment unresolved. Speed-set1585cases diagnostic only. Seven target records received selected primary passages from sixHTMLsnapshots; no whole-body,successor or dependency audit.

Retain missing bs4,follow-on missing binding file,truncated display and version alignment limits. No acceptance upgrade from integrity. Claude r504 remains rate-limited/unreviewed;Sol r522 continues;reserve new disjoint fifty forSol r524. Existing adjudications and counts9additional/39total/next40 unchanged. Root executes no upstream verifier or mathematical checker; only administrative/file/corpus reconciliation.
''')+")\n"+s[b:]
s=s.replace("for num in [520,522]:assert set(j(P/f'reserved-ids-r{num}.json')['ids'])=={r['mathdb_id'] for r in j(P/f'queue-r{num}.json')}","assert set(j(P/'reserved-ids.json')['ids'])=={r['mathdb_id'] for r in j(P/'queue.json')}")
s=s.replace("'coverage':4083,'new_literal_reviews':100","'coverage':4133,'new_literal_reviews':50")
(P/'verify.py').write_text(s);print('prepared')
