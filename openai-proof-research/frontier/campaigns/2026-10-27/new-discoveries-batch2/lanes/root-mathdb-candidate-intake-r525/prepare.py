import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r523/verify.py').read_text()
s=s.replace("I=F/'root-mathdb-breadth-intake-r519'","I=F/'root-mathdb-breadth-intake-r523'")
a=s.index('SPEC=');b=s.index('\ndef j(',a)
s=s[:a]+"SPEC=[('sol-mathdb-primary-qualified-breadth-r522',6270,'423482c4ea0b8038811a1cf7296950209cae977acfc3964a046713d329472cfa','root-mathdb-breadth-intake-r519/reserved-ids-r522.json','corpus_chunk','corpus_line','statement_utf8_sha256')]"+s[b:]
s=s.replace("exact(L/'root-mathdb-breadth-intake-r519',j(I/'manifest.json'))","exact(L/'root-mathdb-breadth-intake-r523',j(I/'manifest.json'))")
s=s.replace('len(cov)==4133','len(cov)==4183').replace('len(cov)==4083','len(cov)==4133')
s=s.replace("for path,e in j(F/name/'flat-bindings.json').items():check(pathlib.Path(path),e)","for e in j(F/name/'flat-bindings.json'):check(pathlib.Path(e['path']),e)")
s=s.replace("assert j(F/name/'proposals.json')==[]","proposals=j(F/name/'proposals.json');assert len(proposals)==2 and {p['mathdb_id'] for p in proposals}=={365437,366370}")
a=s.index(" active=[r for r in j(I/'active-breadth-reservations.json')");b=s.index(" (P/'DECISION.md').write_text(",a)
s=s[:a]+''' active=[r for r in j(I/'active-breadth-reservations.json') if r['lane']!='sol-mathdb-primary-qualified-breadth-r522']
 allids={i for r in active for i in r['ids']};assert len(allids)==100
 for r in active:r['other_active_reservations']=sorted(allids-set(r['ids']));r['active_hypothesis_ids']=[366370];r['protected_ids']=sorted(set(r['protected_ids'])|{366370,365437,365439})
 write('active-breadth-reservations.json',active)
 (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes())
 hypotheses=j(I/'hypothesis-queue.json')
 hypotheses += [{'mathdb_id':366370,'status':'assigned_independent_source_prior_math_review','lane':'sol-mathdb-ordinal-balls-preliminary-review-r526','credit':0},{'mathdb_id':365437,'related_ids':[365439],'one_family':True,'status':'queued_source_first_independent_review','credit':0}]
 write('hypothesis-queue.json',hypotheses)
 write('candidate-briefs.json',j(F/SPEC[0][0]/'proposals.json'))
'''+s[b:]
a=s.index(" (P/'DECISION.md').write_text(");b=s.index(' files=[]',a)
s=s[:a]+" (P/'DECISION.md').write_text("+repr('''# Root r525 candidate intake

Reconcile r522's fifty literal reviews with exact corpus hashes and assignment. Latest coverage4,183 reported literal reviews; two conditional family briefs, zero acceptance/credit. Root has not executed mathematical checkers or certified either claimed counterexample. Existing counts9additional/39total/next40 unchanged.

Route366370 first: reported four-point ordinal rank matrix with nine balls below ten is a very small full-scope negation candidate. Source axioms, ball conventions, distinctness quantifiers, entire source-internal boundary and closest prior/successor bodies require independent qualification. Metric lifting itself is source Proposition1.5 and earns no credit. Allocate separate Sol r526 review; no Lean or manuscript now.

Queue365437/365439 together as one stack-fiber family for a separate source-first review when a Sol slot opens. Candidate reports n5 second-largest fiber5 rather than4, and n8 tie64 at a distinct output defeating uniqueness. Source transition convention and actual journal version may change the scope; published Discrete Mathematics349(3),114834 is metadata-only, typeset body unread. No formal investment or novelty claim. Do not bundle its mathematics into the ordinal review.

Preserve limited four-primary selected-passage coverage, predecessor-versus-successor version issue for Echeloned Spaces, missing bs4, stopped404 and truncated displays. Other r522 exclusions are known-source/wording-only and earn no credit. No current registry clearance. Root adopts no mathematical verdict from an integrity receipt.

Sol r524 breadth continues. Claude r504 remains rate-limited/unreviewed with its reservation protected. New focused Sol r526 makes two active Sol delegates total. No new breadth allocation until the next useful slot; unchanged6000metadata routing pool retained. Root continues only orchestration and administrative/hash reconciliation.
''')+")\n"+s[b:]
s=s.replace('assert len(seen)==150','assert len(seen)==100')
s=s.replace("assert set(j(P/'reserved-ids.json')['ids'])=={r['mathdb_id'] for r in j(P/'queue.json')}","assert {p['mathdb_id'] for p in j(P/'candidate-briefs.json')}=={365437,366370}")
s=s.replace("'coverage':4133,'new_literal_reviews':50","'coverage':4183,'new_literal_reviews':50")
(P/'verify.py').write_text(s);print('prepared')
