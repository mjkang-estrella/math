from pathlib import Path
import json,hashlib,collections,datetime
R=Path(__file__).resolve().parent;L=R.parent
h=lambda b:hashlib.sha256(b).hexdigest()
put=lambda n,x:(R/n).write_text(json.dumps(x,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
rows=json.loads((R/'records.json').read_text()); a={int(i):(s,r) for i,s,r in (line.rstrip('\n').split('\t',2) for line in (R/'assessments.tsv').open())};assert len(a)==50
primary={399665:('13684',1630,1755),399887:('13940',487,510),399888:('13940',523,534),400122:('14222',92,108),400161:('14226',1430,1486),400237:('14604',464,508)}
out=[]
for x in rows:
 n=int(x['mathdb_id']);s,r=a[n]
 out.append({'mathdb_id':n,'canonical_url':x['canonical_url'],'literal_statement':x['statement'],'literal_statement_sha256':h(x['statement'].encode()),'canonical_record_sha256':h(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()),'disposition':s,'scope_reason_mechanism_obstacle':r,'statement_level':'literal_full_statement_read','primary_level':'relevant_primary_section_read' if n in primary else 'not_read; HOLD on source fidelity, no hardness inference','primary_evidence':{'path':'sources/'+primary[n][0]+'.txt','lines':[primary[n][1],primary[n][2]]} if n in primary else None,'proof_level':('public proof section 6.3 inspected; lower-dimensional and Appendix A dependencies not audited' if n==399665 else 'Theorem 1.1 and portions of Section 2 proof inspected; not independent reproof' if n==400237 else 'primary survey reports algorithm; original proof dependency unread' if n in [399887,399888] else 'no complete full-scope proof reviewed'),'registry_level':'NOT_CLEARED: no current proof-registry head verified; required HOLD before discovery investment','certificate_size':'none proposed','bounded_check_executed':'literal scope comparison only; no numerical or exhaustive sweep','bounded_check_planned':None,'discovery_credit':0})
put('dispositions.json',out);put('proposals.json',[])
# Keep excerpts short. Full downloaded source bytes are separately hashed in payload manifest.
ex=[]
for n,(f,b,e) in primary.items():
 lines=(R/'sources'/(f+'.txt')).read_text().splitlines(); excerpt='\n'.join(lines[b-1:e]);excerpt=' '.join(excerpt.split()[:85]);ex.append({'mathdb_id':n,'path':'sources/'+f+'.txt','inspected_lines':[b,e],'short_excerpt':excerpt})
put('source-excerpts.json',ex)
# Parse bound historical evidence; no inspection of any unassigned scientific statement.
A=L/'root-mathdb-accepted-exclusions-r304';D=L/'root-mathdb-breadth-intake-r439'
accepted=json.loads((A/'accepted-exclusions.json').read_text());hist=json.loads((A/'historical-dispositions.json').read_text());cayley=json.loads((L/'root-mathdb-cayley-review-intake-r363/disposition.json').read_text())
def associated(o):
 z=set()
 if isinstance(o,dict):
  for k,v in o.items():
   if k=='mathdb_id' and isinstance(v,(int,str)):z.add(str(v))
   elif isinstance(v,(list,dict)):z|=associated(v)
 elif isinstance(o,list):
  for v in o:z|=associated(v)
 return z
ids=set(str(x['mathdb_id']) for x in rows);assert not ids&associated(accepted);assert not ids&associated(cayley)
put('administrative-reconciliation.json',{'baseline_reported_distinct_reviews':2383,'new_literal_statement_screens':50,'reported_union_if_root_integrates':2433,'not_whole_corpus_review':True,'assigned_disjoint_from_baseline':True,'r304_accepted_associated_ids_disjoint':True,'r363_associated_ids_disjoint':True,'r304_history_container_type':type(hist).__name__,'accepted_additional':9,'accepted_total':39,'next_global_outcome':40,'changes_to_counts':0,'inherited_denied_routes':'AIM/Kourovka/EGRES; AIProofWatch403; rigid-body/triangle-gap successor403 remain parked','MathDB_requests':0})
put('failures.json',[{'stage':'preflight initial','failure':'r304 manifest is a list, not an object','preserved':'preflight-failure-1.log','corrected':'handle both schemas; all listed hashes rerun successfully'},{'stage':'source/prior completeness','failure':'44 primary sections not reviewed; all current proof registry heads unverified','effect':'No proposals; no clearance inferred; HOLD before any further investment'},{'stage':'proof dependencies','failure':'surface algorithms original dependency proofs and Bloch smoothing dependency not audited','effect':'evidence levels explicitly limited'}])
c=collections.Counter(x['disposition'] for x in out)
(R/'SUMMARY.md').write_text('''# Bounded fifty-record screen — r440

Exactly the r439-assigned fifty records were read literally and scoped; no substitutions. This is a statement screen, not a fifty-primary-body or whole-corpus review. Dispositions: '''+str(dict(c))+'''. No hypothesis briefs (`proposals.json` is empty), no discovery credit, no Lean or manuscript work.

Public-result retirements: 399665 matches FMP Theorem 3 (arXiv:1408.1030v2, 12 January 2016), with the constructive Section 6.3 inspected; smoothing remains an identified dependency. 400237 is already Theorem 1 of its cited primary report and Theorem 1.1 of Alon's author-hosted paper; portions of its proof were inspected. 399887 and 399888 are retired only at **primary-survey-reported algorithm** level: the report explicitly supplies the full problem's algorithms, but their original proof dependencies were not read. None is a new result.

Six assigned entries have relevant primary sections read. Five report landing pages and PDFs and two proof PDFs were downloaded; a download does not count as section or proof review. The remaining forty-four entries retain primary-fidelity HOLD even where a deep/programmatic route is parked. Every entry retains current-registry NOT_CLEARED. Search leads (including asymptotic versus ordinary resurgence) do not clear proof scope. No numerical experiments were used to promote a candidate. The decisive bounded work was literal/source scope comparison and proof-endpoint comparison, not a finite sweep.

Bindings are flat references to actual originals, with SHA256 and byte sizes. The gate validated r439's direct bound originals and all listed manifest entries in r439, r301 (including twenty in-place corpus chunks), r304 and r363 before reading scientific content. No upstream verifier was run and no upstream receipt written. Initial schema failure and corrected successful gate are retained. `verify.py` independently rechecks originals, upstream manifest entries, assignment/disjointness, all literal/canonical record hashes and exact local payload membership. Run it through the prescribed helper guard; it writes no receipt. `seal.py` creates the separately excluded final receipt only after a successful run.

No MathDB requests (the inherited 429 HOLD is respected); no barred routes, browser, account, git, public edits, uploads or messages. Current proof-registry clearance is missing, not presumed. The source HTTP downloads succeeded; no 403/429 was retried. Counts remain **9 additional / 39 total / next 40**. Baseline 2383 plus these fifty could become 2433 reported statement screens only after root integration; this packet changes no shared ledger.

Run from this lane's directory:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 -B verify.py
```
''')
print(dict(c))
