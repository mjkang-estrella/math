import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r597/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r595','root-mathdb-breadth-intake-r597').replace('root-mathdb-breadth-intake-r593/reserved-ids.json','root-mathdb-breadth-intake-r595/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r594','sol-mathdb-primary-qualified-breadth-r596').replace('sol-mathdb-primary-qualified-breadth-r598','sol-mathdb-primary-qualified-breadth-r600')
s=s.replace("3952,'e19789ee362f3267eac85ff59313959bc0ab499370882a6bdd61915b27065c8d'","4296,'d2d6be5567fa5cbd78b4a85b412736cca7f6eb247106508fb333993ab41614df'")
s=s.replace("'corpus_chunk','corpus_line','statement_utf8_sha256'","'corpus_path','corpus_line_1based','statement_utf8_sha256'")
s=s.replace('5883','5933').replace('5833','5883')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r599 reconciliation

Reconciled r596: fifty disjoint literal record reviews, zero proposals or credit. Cumulative coverage is 5,933 record reviews, not complete-statement or whole-corpus technical coverage. Preserve 30 self-contained literal assessments/20 definition-restoration judgments and all prior flags.

Three selected primary passages and one selected successor proof body read. 317193 weak endpoint is a public theorem with strict-wording equality caveats; 319095 exact source conjecture follows in its public source from unaudited measure/variational dependencies. 318548 literal sublattice claim has a short classical Birkhoff/Boolean-block route; bounded-embedding strengthening not claimed. Diagnostic block checks do not earn credit. No full dependency or current registry clearance.

Retain descriptive/corrupt records, source/provenance limits and truncated-output followups. No new HTTP failure or parked-route retry. Root performs administrative integrity/corpus reconciliation only, never upstream or mathematical checkers. Adjudications unchanged.

Sol r598 continues. Fifty fresh disjoint records reserved for Sol r600. Claude r504 remains rate-limited with fifty reserved unreviewed IDs. No user input pending. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
routefn='''def routing_pool():
 old=[json.loads(l) for l in (I/'routing-queue.jsonl').open()];oldids={r['mathdb_id'] for r in old};assert len(old)==len(oldids)==6000
 ref=next(e for e in j(P/'bindings.json') if e['original'].endswith('screening-tags.jsonl'));p=pathlib.Path(ref['original']);check(p,ref)
 cm=j(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');expected=next(e for e in cm['files'] if e['path']=='tags/screening-tags.jsonl');check(p,expected)
 extra=[]
 for line in p.open():
  r=json.loads(line)
  if r['mathdb_id'] not in oldids and r.get('status')=='open' and r.get('statement_completeness')=='full':extra.append({k:r[k] for k in old[0] if k in r})
 extra.sort(key=lambda r:(-r['review_priority_score'],r['mathdb_id']));assert len(extra)>=2000
 out=old+extra[:2000];assert len({r['mathdb_id'] for r in out})==8000
 return out
'''
s=s.replace('def validate():',routefn+'def validate():')
s=s.replace(" route=[json.loads(l) for l in (I/'routing-queue.jsonl').open()];assert len(route)==6000\n (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes())", " route=routing_pool()\n (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes()+''.join(json.dumps(r,ensure_ascii=False,sort_keys=True)+'\\n' for r in route[6000:]).encode())\n write('routing-expansion.json',{'prior_rows':6000,'added_rows':2000,'total_rows':8000,'new_technical_reviews':0,'criterion':'Remaining open/full inventory-tag records sorted descending review_priority_score then ascending mathdb_id; metadata routing only, no completeness endorsement'})")
s=s.replace(" assert (P/'routing-queue.jsonl').read_bytes()==(I/'routing-queue.jsonl').read_bytes()", " route=routing_pool();assert [json.loads(l) for l in (P/'routing-queue.jsonl').open()]==route\n assert (P/'routing-queue.jsonl').read_bytes().startswith((I/'routing-queue.jsonl').read_bytes())")
s=s.replace('Fifty fresh disjoint records reserved for Sol r600.', 'Fifty fresh disjoint records reserved for Sol r600. Exhausted 6,000-row routing expanded to 8,000 via inventory-bound metadata only; adds zero technical reviews. Initial failed routing assertion retained in FAILURES.md.')
(P/'verify.py').write_text(s)
print('prepared')
