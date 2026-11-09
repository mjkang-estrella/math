from pathlib import Path
import json,hashlib,collections
O=Path(__file__).resolve().parent;L=O.parent
J=lambda p:json.loads(p.read_text())
def put(n,x): (O/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
rows=J(O/'assigned-records.json');assignment=J(L/'root-mathdb-breadth-intake-r433/reserved-ids.json');ids=set(assignment['ids']);baseline=J(L/'root-mathdb-breadth-intake-r433/coverage-delta.json')
assert len(baseline)==2233 and len(ids)==50 and not ids&set(map(int,baseline))
assert not ids&set(assignment['other_active_reservations'])
assert not ids&{372627,372628,368940,404067,364119}
# Read administrative history in place, extracting only assigned IDs if present.
acc=J(L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json');hist=J(L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json')
hits=[]
def walk(x,path):
 if isinstance(x,dict):
  if x.get('mathdb_id') in ids:hits.append({'path':path,'entry':x})
  for k,v in x.items():
   if k in set(map(str,ids)):hits.append({'path':path+'/'+k,'entry':v})
   walk(v,path+'/'+k)
 elif isinstance(x,list):
  for i,v in enumerate(x):walk(v,path+'/'+str(i))
walk(acc,'accepted-exclusions');walk(hist,'historical-dispositions')
put('administrative-check.json',{'baseline_distinct_reported_statement_reviews':len(baseline),'assigned':len(ids),'other_active':len(assignment['other_active_reservations']),'assigned_history_hits':hits,'cayley_exclusion_read':True,'counts':{'additional':9,'total':39,'next':40},'history_note':'No chronology or publication priority clearance follows from absent ID matches.'})
ranges={'2012-24.txt':[(316,359),(2418,2476)],'2012-25.txt':[(600,680)],'2012-31.txt':[(1525,1542),(1690,1828)],'2012-35.txt':[(1836,2013)],'2012-19.txt':[(510,563)],'2011-53.txt':[(1460,1508),(1715,1746),(2776,2823)],'mathias.txt':[(75,103),(494,621)],'ellipsoids.txt':[(190,244),(2988,3012)]}
ex=[]
for name,rr in ranges.items():
 lines=(O/'primary'/name).read_text().splitlines()
 for a,b in rr:ex.append({'path':'primary/'+name,'lines':[a,b],'text':'\n'.join(lines[a-1:b]),'level':'selected_source_body_section_not_entire_paper_dependency_audit'})
put('excerpts.json',ex)
primary={397422:'2011-53.txt',397427:'2011-53.txt',397436:'2011-53.txt',397624:'2012-19.txt',397671:'2012-24.txt',397693:'2012-24.txt',397713:'2012-25.txt',397715:'2012-25.txt',397814:'2012-31.txt',397815:'2012-31.txt',397876:'2012-35.txt',397877:'2012-35.txt'}
successor={397525:'mathias.txt',397877:'ellipsoids.txt'}
a={}
for line in (O/'assessments.tsv').read_text().splitlines():
 i,status,scope,reason=line.split('\t');a[int(i)]=(status,scope,reason)
assert set(a)==ids
out=[]
for x in rows:
 r=x['record'];i=r['mathdb_id'];status,scope,reason=a[i]
 out.append({'mathdb_id':i,'literal_statement':r['statement'],'literal_statement_sha256':x['literal_statement_sha256'],'canonical_statement_sha256':sha(json.dumps(r['statement'],sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()),'canonical_record_sha256':x['canonical_record_sha256'],'original_chunk':x['original'],'original_line':x['line'],'canonical_url':r['canonical_url'],'source_url':r['source_url'],'scope_quantifiers':scope,'disposition':status,'reason_and_mechanism':reason,'primary_level':'selected_original_report_section_read' if i in primary else 'not_read','primary_section_file':'primary/'+primary[i] if i in primary else None,'successor_level':'selected_theorem_and_concluding_proof_read' if i in successor else 'not_qualified','successor_file':'primary/'+successor[i] if i in successor else None,'full_proof_dependencies_audited':False,'registry_level':'HOLD_current_registry_unavailable_no_clearance','prior_cleared':False,'source_scope_cleared':False,'executed_calculation':'none; statement and source-body reasoning only','small_certificate_route':'See reason_and_mechanism; no new certificate produced','accepted_credit':0})
put('dispositions.json',out);put('proposals.json',[])
put('failures.json',[{'kind':'inherited_access_HOLD','routes':['MathDB 429','AIM/Kourovka/EGRES denied','AIProofWatch 403','rigid-body successor 403','triangle-gap successor 403'],'attempted_this_lane':False,'handling':'No retries or alternate-route fishing; current registry remains HOLD.'},{'kind':'scope_protocol_deviation','detail':'Before the assigned-only extractor, a native head -c 1500 read of original chunk0001 displayed the unassigned ID1 schema record. No substitution, disposition, technical assessment or coverage credit was made for it. It was after manifest freeze. Preserve this deviation rather than claim strict assigned-only display compliance.'},{'kind':'search_result_only','detail':'Public search returned a ScienceDirect result automatically. No ScienceDirect URL was opened or downloaded. Only author-hosted Mathias PDF used for body evidence.'}])
put('registry-check.json',{'date':'2026-10-31','status':'HOLD','current_head':None,'reason':'Inherited public proof-registry access failures not retried. No candidate promoted or novelty clearance claimed.','significant_proof_investment':False})
put('search-notes.json',{'date':'2026-10-31','queries':['site.ems.press 11793 2012 31 Oberwolfach kernels','site.ems.press 11786 2012 24 collapsible manifold','site.ems.press 12007 2012 35 McDuff Schlenk','site.ems.press 11787 2012 25 trace free','compactly supported infinitely differentiable radial positive definite kernel explicit formula','Mathias Cohen n-generics computes','transcendental L2-Betti Grabowski 2010','ellipsoids balls McDuff Schlenk 2012 embedding capacity'],'usable_primary_body_urls':['https://math.berkeley.edu/~slaman/papers/Mathias_generics.pdf','https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p05-p.pdf'],'note':'Search snippets are leads only, not proof-body or registry clearance; downloaded bytes separately retained.'})
sourcebytes=[]
for p in sorted((O/'primary').iterdir()):sourcebytes.append({'path':str(p.relative_to(O)),'size':p.stat().st_size,'sha256':sha(p.read_bytes()),'kind':'downloaded_pdf' if p.suffix=='.pdf' else 'pdftotext_layout_derivative'})
put('sourcebytes.json',sourcebytes)
put('provenance.json',{'binding_style':'flat actual originals, no corpus copies or recursive binding expansion','binding_file':'bindings.json','assignment_origin':str(L/'root-mathdb-breadth-intake-r433/reserved-ids.json'),'corpus_origin':str(L/'pi-mathdb-full-corpus-inventory-r301/corpus'),'statement_hash_encoding':'literal UTF8 without normalization','canonical_hash_encoding':'json.dumps(sort_keys=True,ensure_ascii=False,separators=(comma,colon)).encode(UTF8); whole original record and statement JSON string hashed separately','download_bytes':'sourcebytes.json','source_excerpts':'excerpts.json','freeze_before_science':'freeze-receipt.json','inherited_exclusions':'administrative-check.json','counts_unchanged':[9,39,40]})
counts=collections.Counter(d['disposition'] for d in out)
(O/'SUMMARY.md').write_text('''# r434 bounded fifty-record screen

Exactly fifty assigned cached statements were read literally and assessed for scope, quantifiers and a concrete mechanism/obstacle. No proposals survive this bounded screen. This is not a whole-corpus technical review or a claim that any question is currently open, solved, novel or accepted.

The original r433 manifest (51 entries), r301 manifest (128 entries including all twenty original chunks using its bytes field), r304 accepted/history manifest (6 entries), and r363 exclusion manifest (94 entries) passed in-place hash/size validation before scientific or administrative-history reading. r433 direct bound originals were also checked; no recursive bindings expansion or corpus snapshots were made. Flat actual-original references are in bindings.json. Verification executes no upstream verifier and writes no upstream receipt.

Baseline: 2233 distinct *reported* statement reviews, not independently re-reviewed here. This lane adds fifty assigned literal-statement screens, subject to root reconciliation; no overlap with the other active fifty or explicit excluded IDs. Counts remain 9 additional / 39 total / next 40.

Eight PDFs were downloaded (six report bodies and two public proof bodies). Selected sections were read, not entire reports or every proof dependency. The per-record levels distinguish original report sections, successor theorem/concluding proof reading and missing qualification. Mathias Theorem 5.2 has its complete concluding construction/verification read; the original 2012 report convention and small-n boundary were not independently qualified. McDuff–Schlenk's published Theorem 1.1.2 and part(ii) closing proof were read; its full exceptional-curve machinery was not audited. Neither is a new result.

The source report already presents the exact Hamiltonian-square spectral bound, attributes the tree-metric multiflow min–max result, and sketches the explicit full torus filling. Their dispositions retire source-known routes at report evidence level, without pretending full dependency replay. The compact C-infinity kernel source explicitly knows convolution existence; an autocorrelation integral is therefore no new answer to its explicit-formula request. Trace-free surface constraints are tied in the source to Ricci surfaces, and the positive-curvature obstruction is not a new counterexample. Simple Specht-module linear algebra, taut-angle enumeration and finite vertex-subset enumeration are routine algorithms, not discovery hypotheses.

Deep cases are parked with their specific missing universal bound or structural theorem. Scope-corrupted or underspecified statements stay HOLD; missing source/registry access is not evidence of hardness. No expensive scan, new mathematical certificate, Lean, manuscript, MathDB request, public action or current-registry clearance was performed. Inherited denied routes remain parked. All registry-dependent eligibility is HOLD.

Protocol limitation: an initial native chunk-header read accidentally displayed unassigned ID1 as a schema example after freeze. It was not assessed, substituted or counted. This breaches the requested assigned-only display discipline and is recorded in failures.json. A public search also automatically surfaced a barred ScienceDirect result; no such URL was opened. No other lane was written.

Artifacts: dispositions.json has exact literals and both literal and canonical hashes; assessments.tsv contains individual technical reasons; proposals.json is empty; sourcebytes.json/downloads.json/successor-downloads.json and excerpts.json separate downloads from selected body evidence. verify.py checks originals, source manifests, twenty chunks, disjointness, exact statements, hashes and the exact payload file set. final-receipt.json is separate from the payload manifest.

Disposition counts: '''+json.dumps(dict(counts),sort_keys=True)+'\n')
print(dict(counts))
