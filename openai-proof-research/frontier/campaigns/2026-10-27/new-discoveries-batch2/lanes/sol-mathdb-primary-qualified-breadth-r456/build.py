from pathlib import Path
import json,hashlib,datetime,collections,math
L=Path(__file__).resolve().parent
utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
def dump(n,x): (L/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
records=json.loads((L/'records.json').read_text());notes={}
for line in (L/'technical-notes.tsv').read_text().splitlines():
 i,status,passage,obstacle=line.split('\t');notes[int(i)]=(status,passage,obstacle)
assert len(notes)==50 and set(notes)=={x['record']['mathdb_id'] for x in records}
checks=[dict(id='public-hirsch-arithmetic',executed=True,calculation='86 - 43 = 43 < 44',result=86-43<44,purpose='Verify cited public witness parameter inequality only; no polytope replay or discovery credit.'),dict(id='clique-scope-sanity',executed=True,parameters=dict(n=16,d=15,r=1),alpha=1,target_main_term=16*math.log(15)/15,purpose='Illustration only. Decisive family argument: K_(d+1) is linear as a 2-graph, alpha=1 while (d+1)log(d)/d diverges. Missing uncrowded/triangle-free scope is a record/source issue; no credit.')]
dump('bounded-checks.json',checks)
d=[]
for x in records:
 r=x['record'];i=r['mathdb_id'];s,p,o=notes[i];has=p!='NONE'
 d.append(dict(mathdb_id=i,title=r['title'],literal_statement=r['statement'],statement_sha256=x['statement_sha256'],canonical_record_sha256=x['canonical_record_sha256'],original_chunk=x['original_chunk'],original_line=x['original_line'],canonical_url=r['canonical_url'],disposition=s,technical_disposition=o,full_scope=r['statement'],full_literal_statement_read=True,quantifiers_reviewed=True,source_level='primary passage read, retained PDF/text' if has else 'corpus record only; primary body missing',source_passages=p,source_internal_results_checked=has,whole_primary_body_read=False,proof_level='published statement matched; no independent proof-body replay' if s=='EXCLUDE_PUBLIC' else 'no full-scope proof established',dependency_audit='NOT_COMPLETED; no formal claims or imported theorem dependencies accepted',closest_successor_audit='bandwidth theorem matched' if i==316506 else ('Santos counterexample matched' if i==316162 else 'HOLD: incomplete; absence of search hits has no novelty implication'),registry_level='HOLD: zero MathDB requests; inherited 429; no live resolution/priority clearance',bounded_check_status='executed limited sanity check; not full-scope proof' if i in (405060,316162) else 'not executed: no decisive bounded full-scope test identified',bounded_check_reference='bounded-checks.json' if i in (405060,316162) else None,decisive_calculation='none executed that establishes a new full-scope result',certificate_size='no new complete certificate',formal_dependencies='not selected; Lean and manuscript work not started',strongest_objection=o,prior_gaps='Live registry and comprehensive successor/dependency audit unresolved. This screening cannot certify novelty.',accepted_credit=0,proposal=False))
dump('dispositions.json',d);dump('proposals.json',[])
sources=[]
for n in ['sources.json','sources-owr.json','sources-more.json']:
 for e in json.loads((L/n).read_text()):
  if e.get('file'):
   p=L/e['file'];assert sha(p.read_bytes())==e['sha256']
   t=p.with_suffix('.txt')
   if p.suffix=='.pdf' and t.exists():
    e['text_file']=str(t.relative_to(L));e['text_sha256']=sha(t.read_bytes());e['body_read_scope']='selected passages only; whole body and dependency audit not completed';e['version_front_matter']=t.read_text()[:1800]
  sources.append(e)
dump('source-provenance.json',sources)
dump('search-leads.json',dict(utc=utc,scope='One web search call for bandwidth successor, preferential-attachment successor, colliding permutations. Search snippets are leads only, not source proof or registry evidence.',queries=['Böttcher Schacht Taraz proof bandwidth theorem arxiv','preferential attachment diameter typical distance Dommers van der Hofstad Hooghiemstra 0705.4153 constants successor','colliding permutations conjecture solved 2025 2026'],leads=[dict(url='https://www.math.uni-hamburg.de/home/schacht/2009/bolkomr.pdf',retained=True),dict(url='https://onlinelibrary.wiley.com/doi/full/10.1002/rsa.20798',retained=False,status='HOLD: search lead only, no body requested')],mathdb_search_snippet='Incidental unrelated MathDB result not opened or used; zero direct MathDB requests.'))
dump('failures.json',[dict(kind='local_preflight_schema',retained_log='preflight-failure-1.log',reason='r304 manifest is a list, not files object',resolution='independent parser accepts both; rerun PASS'),dict(kind='inherited_access_hold',service='MathDB',status='429 HOLD inherited; zero requests'),dict(kind='inherited_parked_routes',routes=['AIM/Kourovka/EGRES','AIProofWatch','rigid-body','triangle-gap'],attempted=False),dict(kind='evidence_gaps',status='HOLD',details='No primary source obtained for record-only rows; comprehensive closest-successor, registry and dependency audits incomplete. All disclosed individually.')])
counts=collections.Counter(x['disposition'] for x in d)
dump('review-counts.json',dict(assigned=50,full_literal_statements_read=50,primary_passage_rows=sum(x['source_passages']!='NONE' for x in d),dispositions=dict(counts),proposals=0,new_credit=0,baseline_reported_statement_reviews=2783,root_reconciliation_required=True,additional=9,total=39,next=40))
summary=f'''# r456 breadth screening — zero proposals

All fifty assigned full literal statements and quantifiers were read. No full-scope new result is proposed. Exactly fifty individual dispositions preserve their literal UTF-8 statements, statement hashes, canonical normalized-record hashes, and original chunk/line. Baseline reported reviews remain 2,783 until root reconciles; this lane does not alter that ledger. Campaign counts unchanged: **9 additional / 39 total / next 40**.

The distribution is {dict(counts)}. Primary **passages** were read for {sum(x['source_passages']!='NONE' for x in d)} rows; this is not whole-body review, proof replay, or dependency audit. Missing primary sources are HOLD, never hardness certifications. Deep targets with primary passages are parked with successor/registry HOLD. Metadata and source retrieval alone are not counted as technical review.

## Main findings

- 316162: Santos arXiv:1006.2814v3 states a bounded 43-dimensional, 86-facet counterexample of diameter at least 44. Only the statement and parameter inequality were checked, not the construction dependencies. Public result; zero credit.
- 316506: Csaba Conjecture 13 matches Böttcher–Schacht–Taraz Theorem 1 in the author PDF dated August 12, 2008. The theorem has the same parameter order and embedding conclusion. Public result; no independent proof-body replay.
- 316614: source Definition 3.2 uses inf(relators minus generators), opposite to the record's convention. Sign-based refutation would be a source-transcription repair, excluded from credit. Intended conjecture has a source computability obstruction.
- 405060: literal r=1 permits cliques. Their independence number is one whereas the asserted main term diverges with degree. This exposes a missing hypothesis in the recorded/source formulation and earns no credit; no repaired higher-uniformity target is substituted.
- 315977: arbitrary unbounded forests include the whole plane, where no rectifiable escape curve exists. This domain/attainment defect is not a discovery; primary scope remains HOLD.
- 404978 and 405077: source-internal classification or bounds and omitted hypotheses/dimensions must be resolved before any investment. Neither an already classified log-canonical surface nor an unrestricted full-rank output matrix supplies a new target resolution.

## Scope and integrity

`preflight.py` independently checked the intake manifest and every direct binding's actual original before scientific/history reading. It bound and verified r304 and r363 manifests before their scientific contents were read. Twenty inventory chunks were checked **in place** against byte sizes and SHA-256; no corpus copy was made. Inventory `frozen_inputs` membership is listed separately. Bindings are flat paths and hashes: no recursive binding/history expansion and no upstream verifier execution. The accepted/historical exclusion JSON, coverage, other active r454 reservation and five explicit excluded IDs are checked against the exact assignment. Queue order is retained, with no substitutions.

The first preflight invocation failed because the r304 manifest is a list. Its failure log is retained, the parser was corrected, and the second invocation passed before statement extraction. All helper executions used the specified guard, environment and Python flags; limits were not raised. No Lean, manuscript, large search or corpus computation was run. External retrievals retained URLs, UTC retrieval times, headers, bytes, hashes and PDF version front matter. Source text derivatives are separately hashed. One web search supplied successor leads; unretained snippets have no proof or novelty standing. No direct MathDB, Google, GitHub, ScienceDirect, denied inherited route, browser, account or publication request was made. No HTTP 403/429/challenge response occurred in this lane's retained fetches; inherited MathDB 429 HOLD remains active.

`verify.py` rechecks actual originals, the twenty chunks, inventory frozen membership, exact assignments and exclusions, literal and canonical record hashes, retained source bytes, and the exact payload file set. It exits nonzero on mismatch. The manifest excludes only itself and the separate final receipt. **Integrity PASS is not mathematical or novelty PASS.** Root alone reconciles the fifty reviews and decides acceptance; no new accepted result or count increment is asserted.

## Files and review limits

`technical-notes.tsv` contains one concrete full-scope mechanism/obstacle per record. `dispositions.json` separately records source, proof, registry, bounded-check, certificate and dependency levels. `bounded-checks.json` contains two limited sanity calculations, neither a new-result certificate. `proposals.json` is empty. Source/closest-successor audits remain incomplete wherever explicitly marked HOLD; this packet is screening, not a comprehensive literature audit. No novelty inference is made from absent hits.
'''
(L/'SUMMARY.md').write_text(summary)
print(json.dumps(dict(counts)));print('50 dispositions; 0 proposals; sources sealed by content hash')
