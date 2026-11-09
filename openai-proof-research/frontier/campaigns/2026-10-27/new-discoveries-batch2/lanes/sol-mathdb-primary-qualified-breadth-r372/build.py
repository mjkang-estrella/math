from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).parent;P=L.parent
rs=json.loads((L/'records.json').read_text()); notes={}
for s in (L/'disposition-notes.tsv').read_text().splitlines():
 i,d,r=s.split('\t');assert int(i) not in notes;notes[int(i)]=(d,r)
assert len(notes)==50 and set(notes)=={r['mathdb_id'] for r in rs}
primary={396092:['simplex-body','simplex-successor'],396646:['toric-body','toric-arxiv-successor'],397326:['cover-shift-body','cover-successor'],397342:['cover-shift-body','shift-successor'],399289:['polygon-body','polygon-successor'],397763:['bj-successor']}
proof={396092:'selected concluding degree-26-majorant proof section; moments and cited geometric dependencies not independently validated',396646:'Example 4.6 pp15–16 read, p15 visually inspected; Corollary 4.4 and Klyachko dependencies not completely validated',397342:'Theorem 1.2 and Lemma 3.1 proof read; remaining stage proofs/dependencies not completely reviewed',397763:'Theorems 1.2–1.3 and four-knot proof mechanism read; enumeration not replayed'}
rows=[]
for r in rs:
 i=r['mathdb_id'];d,reason=notes[i]
 rows.append(dict(mathdb_id=i,title=r['title'],literal_statement=r['statement'],text_sha256=hashlib.sha256(r['statement'].encode()).hexdigest(),hash_encoding='UTF-8 exact normalized corpus statement; no TeX repair',canonical_url=r['canonical_url'],source_url=r['source_url'],disposition=d,individual_reason=reason,evidence_level='literal_record_plus_selected_primary_body' if i in primary else 'literal_record_only',retained_read_bodies=primary.get(i,[]),selected_proof_section=proof.get(i,'none'),complete_dependencies=False,bounded_novelty='not cleared; no new outcome nominated',credit=0))
(L/'dispositions.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n');(L/'proposals.json').write_text('[]\n')
(L/'provenance.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),corpus='pi-mathdb-full-corpus-inventory-r301/manifest.json; 20 chunks checked in place',baseline='root-mathdb-breadth-intake-r371/coverage-delta.json; root reports 783',request_policy='429HOLD: zero MathDB requests; no browser, Google, GitHub endpoints, ScienceDirect direct requests, external messages or mutations',search='web search discovery leads only, three calls; queries recorded in source-notes.md; incidental search results on excluded domains not opened or used',scope='selected excerpts only, not whole papers or dependency closure',counts=dict(additional=9,total=39,next=40),qualification='Open labels and empty solutions confer no novelty; source-internal examples and successor scope checked before any mathematical computation'),indent=2)+'\n')
# Direct record association/history check, without claiming a full textual semantic proof.
a=json.loads((P/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json').read_text());h=(P/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json').read_text()
ids=set(notes);assoc=[]
for f in a['families']:
 for r in f.get('record_associations',[]):
  if r.get('mathdb_id') in ids:assoc.append(r)
(L/'exclusion-check.json').write_text(json.dumps(dict(accepted_families_read=39,direct_accepted_association_matches=assoc,historical_id_mentions=[i for i in ids if str(i) in h],cayley_excluded=364119,cayley_present=364119 in ids,cayley_rule='A published source-internal literal negation subsumes another witness; smaller witnesses and unlabelled contradictions still credit zero',semantic_limit='Scope summaries read; no new proof offered, no global priority clearance'),indent=2)+'\n')
(L/'capped-checks.json').write_text(json.dumps(dict(command_prefix='OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B',guard=str(P/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),caps=dict(address_space_MiB=512,group_RSS_MiB=512,CPU_seconds=210,wall_seconds=230),mathematical_sweeps=0,new_ordinary_results=0,formal_work=0,corpus_chunks_verified=20,literal_reviews=50,ids_with_selected_primary_body=6,original_problem_bodies=5,successor_bodies=6,complete_dependency_closures=0,proposals=0,failures='failures.md'),indent=2)+'\n')
