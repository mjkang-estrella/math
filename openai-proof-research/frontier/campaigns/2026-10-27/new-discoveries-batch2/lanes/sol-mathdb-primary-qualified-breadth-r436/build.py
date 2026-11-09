from pathlib import Path
import json,hashlib,math,itertools,datetime,collections
O=Path(__file__).parent;L=O.parent;R=L.parents[4]
def sha(b):return hashlib.sha256(b).hexdigest()
def canon(x):return json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()
def write(n,x): (O/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
r=json.loads((O/'records.json').read_text()); rows={int(i):(d,s) for i,d,s in (x.split('\t',2) for x in (O/'assessments.tsv').read_text().splitlines())}; assert len(rows)==50
ex=[]
for id,a,b in [(12330,2422,2538),(12490,753,918),(12493,277,341),(12594,1731,1865),(12723,2204,2338),(12861,1462,1664)]:
 p=O/f'sources/{id}.txt';lines=p.read_text().splitlines();ex.append({'source':str(p.relative_to(O)),'first_line':a,'last_line':b,'text':'\n'.join(lines[a-1:b]),'evidence':'report contribution sections only; not full report or cited proof dependencies'})
write('source-excerpts.json',ex)
checks=[]
from fractions import Fraction
for X in [(1,),(1,2),(1,1,2),(2,3,4),(1,2,2,3,4)]:
 m=len(X);dp={(0,0):1}
 for x in X:
  nd=dp.copy()
  for (t,s),c in dp.items():nd[t+1,s+x]=nd.get((t+1,s+x),0)+c
  dp=nd
 for k in range(-1,sum(X)+2):
  f=sum((Fraction(dp.get((t,k),0),math.comb(m,t)) for t in range(1,m+1)),Fraction())
  hits=sum(k in list(itertools.accumulate(P)) for P in itertools.permutations(X));g=Fraction(hits,math.factorial(m));assert f==g
  checks.append({'X':X,'k':k,'coefficient_probability':str(f),'permutation_probability':str(g)})
write('bounded-calculation.json',{'id':398778,'scope':'five assigned-problem test multisets, labelled permutations, all k from -1 to n+1; validation only','checks':checks,'proof':'For t>=1 a uniform prefix is a uniform t-element labelled subset. Strict positivity implies at most one t hits k, so sum probabilities. Coefficients count such subsets. This is a routine exact identity, not a sharp uniform asymptotic.','complexity':'O(m^2 n) integer DP operations for all subset cardinalities and sums; m*n coefficient cells, bit lengths at most m+1. No small asymptotic certificate for arbitrary n claimed.'})
# Read and reconcile only the administrative indices; no upstream verifier executed.
accepted=json.loads((L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json').read_text());history=json.loads((L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json').read_text());cayley=json.loads((L/'root-mathdb-cayley-review-intake-r363/disposition.json').read_text())
# Textual ID hits are leads only, deliberately not mathematical clearance.
joined={str(x['mathdb_id']):{'accepted_index_id_hit':str(x['mathdb_id']) in json.dumps(accepted),'historical_index_id_hit':str(x['mathdb_id']) in json.dumps(history)} for x in r};write('administrative-reconciliation.json',{'accepted_family_count':accepted['accepted_family_count'],'assigned_id_leads':joined,'cayley_exclusion_id':cayley['mathdb_id'],'not_current_registry_clearance':True})
sources={398224:12330,398440:12490,398483:12493,398659:12594,398674:12723,398776:12861,398778:12861}
out=[]
for x in r:
 id=x['mathdb_id'];d,s=rows[id];primary=id in sources
 out.append({'mathdb_id':id,'title':x['title'],'literal_statement':x['statement'],'literal_statement_sha256':sha(x['statement'].encode()),'canonical_record_sha256':sha(canon(x)),'canonical_encoding':'sorted keys, ensure_ascii=False, compact separators, UTF-8','source_url':x['source_url'],'scope_and_reason':s,'disposition':d,'statement_level':'full literal cached statement read','primary_level':'relevant report contribution body inspected' if primary else 'not inspected (398219 report downloaded only)' if id==398219 else 'not inspected','primary_section':f'sources/{sources[id]}.txt; source-excerpts.json' if primary else None,'proof_level':'report proof mechanism inspected; cited dependency proofs not inspected' if id in [398224,398440,398483] else 'elementary subset-counting argument plus bounded exact check; routine and uncredited' if id==398778 else 'no complete full-scope proof inspected or constructed','successor_level':'not checked; no investment brief','registry_level':'HOLD: current public registry heads and exact-scope proof bodies not obtained','prior_cleared':False,'source_scope_cleared':id in [398224,398440,398483,398778],'credit':0,'brief':False,'calculation':'executed in bounded-calculation.json' if id==398778 else 'none executed; mechanism/obstacle assessment only'})
write('dispositions.json',out);write('proposals.json',[])
write('provenance.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'exactly assigned fifty; no corpus-wide technical-review claim','originals':'bindings.json, flat references only; no copies or expansion of nested bindings','preflight':'all four supplied manifests validated before scientific reading; r435 direct bindings validated; 20 r301 original chunks verified in place using bytes fields','network':'six EMS primary landing pages and their advertised six PDFs; zero MathDB, Google, GitHub, ScienceDirect, browser, account or publication requests','current_registry':'not obtained; HOLD, no novelty clearance','versions':'fixed 2013/2014 OWR published reports, downloaded bytes bound in payload manifest; no successor versions inspected','counts':{'additional':9,'total':39,'next':40},'evidence_counts':{'cached_literal_statements_read':50,'primary_report_pdfs_downloaded':6,'target_records_primary_sections_inspected':7,'complete_external_dependency_proofs_checked':0,'successor_proof_bodies_checked':0,'briefs':0}})
counts=collections.Counter(x['disposition'] for x in out)
(O/'SUMMARY.md').write_text('''# Bounded fifty-record screen — r436

Completed the exact fifty r435 assignments from full literal cached statements. No substitutions, hypotheses delegated, credit, novelty or acceptance claims. Proposals: **0**. Counts remain **9 additional / 39 total / next 40**.

Before scientific reading, validated r435, r301, r304 and r363 manifests, r435 direct bound originals and the twenty r301 original chunks in place, including bytes fields. `bindings.json` contains actual original SHA256 and sizes with flat references; no corpus snapshots or recursive binding expansion.

Read seven target-relevant primary contribution sections in six downloaded OWR reports (not entire reports or all cited proofs). Three exact source-stated theorems retire discovery investment: 398224 (Theorem 40, factor 6 with the exact node bound), 398440 (Theorems 1–3 and printed examples), 398483 (the printed BFM13 bound and Minkowski consequence). These are source-body applicability findings, not independent dependency-proof verification. No closest-successor proof body or current public registry was checked, so there is no registry or novelty clearance.

398778 has a full-scope elementary subset-counting formula, but it is routine and does not supply the sharp quantitative asymptotics already discussed in its report. Executed exact coefficient-versus-labelled-permutation checks on five tiny multisets. No large sweep or proof-credit claim. 398659 has a source/cache formula mismatch and unresolved sharp-constant dependencies; no correction promoted. 398674 requires cancellation-safe complexity analysis beyond the primary report's nonnegative-derivative argument. Zero/constant solutions, unknot endpoints, trivial c=0 choices and missing conjugation are not proposed outcomes.

All other records retain individual quantified obstacles in dispositions.json: broad classification/asymptotic problems are parked; missing source context and current registry evidence are HOLD, never evidence of hardness. No per-record MathDB requests were made. Inherited denied sources were not retried. Access success is distinguished from inspected sections and complete proof dependencies in provenance and dispositions.

Disposition counts: '''+json.dumps(dict(counts),sort_keys=True)+'''.

The verifier independently rehashes originals, validates upstream manifests without executing their verifiers, checks all twenty chunks, assignment/disjointness and exact statement/canonical hashes against the original chunk lines, and enforces the exact payload set. Only manifest.json and final-receipt.json are excluded by exact relative path. Run via the mandated helper guard, as documented in RUN.md. No shared files were changed.
''')
(O/'failures.md').write_text('''# Failures and limits

Initial native read omitted the requested workdir and returned file-not-found; corrected before preflight. No scientific conclusions came from that failed command. All guarded helper runs to this stage passed; guard diagnostics are retained in their logs.

Initial HTML regex found no PDF links because EMS advertises extensionless PDF URLs. Inspected the saved citation_pdf_url metadata and fetched those exact advertised URLs; no denied-route retry or alternate-route fishing. All twelve EMS responses were 200.

No current registry snapshot/head, source successors, or complete external proof dependencies were obtained. These remain HOLD. Inherited AIM/Kourovka/EGRES, AIProofWatch403 and rigid-body/triangle-gap successor403 routes were not used. No MathDB request, hence no new 429. No finite computation certifies novelty or the deep parked families.

One early bounded schema inspection exposed the beginning of an unassigned cached chunk record. It was not assessed, substituted, added to dispositions, used as a schema example in outputs, or counted toward technical coverage. The fifty scientific assessments use only assigned records.
''')
print('built',len(out),dict(counts),'bounded checks',len(checks))
