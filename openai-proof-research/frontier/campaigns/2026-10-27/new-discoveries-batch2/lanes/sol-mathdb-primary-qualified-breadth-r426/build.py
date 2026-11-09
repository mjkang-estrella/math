from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).parent;L=R.parent
canon=lambda x:json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode('utf-8')
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(n,x):(R/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
ass={}
for line in (R/'assessments.txt').read_text().splitlines():
 n,s,r=line.split('|',2);ass[int(n)]=(s,r)
records=json.loads((R/'selected-records.json').read_text());assert set(ass)=={x['mathdb_id'] for x in records}
sections={394408:[('1464.txt',1031,1105)],394683:[('1596.txt',515,562),('1407.4726v2.txt',50,232),('1407.4726v2.txt',230,385)],394897:[('1782.txt',2330,2360)],394904:[('1782.txt',2675,2738)],394923:[('1783.txt',622,676),('1906.10213.txt',290,305),('1906.10213.txt',610,690)]}
rows=[]
for x in records:
 n=x['mathdb_id'];scope,reason=ass[n]
 state='PARK_mechanism_obstacle'
 if 'HOLD' in reason:state='HOLD_source_or_model_qualification'
 if n==394408:state='RETIRE_routine_literal_scalar_conditions'
 if n in [394683,394923]:state='RETIRE_public_theorem_section_qualified'
 if n in [394897,394904]:
  state='RETIRE_source_explicitly_reports_known_result'
  reason+=' Actual original report explicitly states the same result was already proved: 1782.txt lines '+('2338–2343' if n==394897 else '2696–2702')+'. Applicability is identity of graph class, parameter quantifier, and displayed bound; no stronger quantitative constant or small-order assertion is claimed. Original cited proof body not acquired; this is source-reported exclusion, not independently replayed theorem.'
 if n==394683:reason+=' Bridge: source Problem (2) concerns full McCool P Sigma_l, not its upper-triangular subgroup. Successor Theorem 2.1 identifies the same rational cohomology algebra; Proposition 2.3 proves Koszulity for n=2,3 by PBW presentations; Lemma 3.1 propagates non-Koszulity from n=4 by split quotient, Proposition 3.3 reduces to a quotient by a free Lie ideal, and Theorem 3.6 reports degree-eight coefficient 589834 rather than 589824. Small n=1 is the trivial group. The published Bergman/GAP computation was NOT reproduced; reported runtime is up to twelve hours, outside this lane cap. No computational dependency closure claimed.'
 if n==394923:reason+=' Bridge: original Larson Question 2 uses full MM++, not MM++ restricted to continuum-sized posets. Successor v2 Theorem 1.2 states precisely full MM++ implies Woodin Pmax axiom (*). Inspected proof of Theorem 2.12 from Lemma 2.14 uses saturation of NS_omega1 and Sigma1 forcing absoluteness to meet each dense set. Lemma 2.14 forcing construction and external determinacy/inner-model dependencies are NOT fully read or revalidated. This is a theorem-and-reduction-qualified public exclusion, not independent proof verification.'
 rows.append({'mathdb_id':n,'canonical_url':x['canonical_url'],'literal_statement':x['statement'],'statement_sha256':sha(x['statement'].encode()),'canonical_record_sha256':sha(canon(x)),'scope':scope,'reason':reason,'disposition':state,'credit':0,'mechanism_calculation': 'Executed exact Fraction arithmetic: for alpha=delta^(1/2), 1-(3/2)(1/2)=1/4>0, so both scalar limits hold.' if n==394408 else 'No new mathematical computation executed; bounded statement/mechanism assessment only. Public computed obstruction for 394683 was read, not rerun.','certificate_size_formal_dependencies':'No proposed certificate or formalization. General mechanism obstacle stated in reason.','evidence_levels':{'literal_cached_statement_read':True,'primary_problem_body_read':n in sections,'successor_proof_body_read': 'selected proof sections only' if n in [394683,394923] else False,'full_successor_proof_read':False,'dependency_closure_checked':False,'current_public_registry':'HOLD: no current registry head acquired; inherited denied routes parked; barred GitHub API/raw/codeload/diff not used','cached_registry':'r304 accepted/history originals hash-bound; r363 Cayley exclusion retained; administrative evidence only'},'inspected_sections':[{'file':'primary/'+f,'lines':[a,b]} for f,a,b in sections.get(n,[])],'prior_cleared':False})
put('dispositions.json',rows);put('proposals.json',[])
# Exact bounded scalar calculation, no numeric limiting experiment.
from fractions import Fraction
assert 1-Fraction(3,2)*Fraction(1,2)==Fraction(1,4)
put('calculation.json',{'id':394408,'alpha_exponent':'1/2','noise_ratio_exponent':str(1-Fraction(3,2)*Fraction(1,2)),'claim':'literal scalar limits only; routine, credit 0'})
ex=[]
for n,ss in sections.items():
 for f,a,b in ss:
  lines=(R/'primary'/f).read_text().splitlines();ex.append({'id':n,'file':'primary/'+f,'first_line':a,'last_line':b,'text':'\n'.join(lines[a-1:b])})
put('excerpts.json',ex)
put('failures.json',[{'stage':'freeze initial','kind':'local schema assumption','evidence':'freeze-run.log','resolved':'freeze-run-2.log verifies list-style hash-only r304 manifest and retains actual sizes'},{'stage':'current public proof registry','kind':'HOLD_no_current_registry','reason':'No current registry head acquired. Inherited AIM/Kourovka/EGRES and AIProofWatch 403 routes remain parked; no requests or alternate-route fishing.'},{'stage':'all bodies not listed in excerpts','kind':'not_attempted_bounded_screen','reason':'Statement-only obstacle assessment; no source clearance or hardness claim.'}])
# Flat hashes of retained downloads/derived text, distinct from originals.
put('sourcebytes.json',[{'path':str(p.relative_to(R)),'sha256':sha(p.read_bytes()),'size':p.stat().st_size,'role':'downloaded' if p.suffix in ['.pdf','.html'] else 'pdftotext derived; only listed excerpts inspected'} for p in sorted((R/'primary').iterdir())])
put('provenance.json',{'assignment':'root-mathdb-breadth-intake-r425/reserved-ids.json and queue.json','baseline':2033,'reviewed_this_lane':50,'proposals':0,'coverage_claim':'exact assigned cached statements only; no whole-corpus claim','counts':{'additional':9,'total':39,'next':40},'MathDB_requests':0,'current_registry_clearance':False,'freeze_before_scientific_read':'freeze-receipt.json; initial failed schema attempt preserved','upstream_verifiers_executed':False,'bound_originals':'bindings.json flat paths, SHA256 and actual sizes; no recursive binding expansion','successor_versions':{'1407.4726':'v2 17 February 2015','1906.10213':'v2 18 March 2021, internal date March 19 2021'},'timestamp':datetime.datetime.now(datetime.timezone.utc).isoformat()})
# Reconcile cached accepted/history registries only, without treating metadata as proof review.
reg={}
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 obj=json.loads((L/'root-mathdb-accepted-exclusions-r304'/name).read_text());s=json.dumps(obj)
 reg[name]={'assigned_id_string_matches':[x['mathdb_id'] for x in records if str(x['mathdb_id']) in s],'scope':'administrative matching only; no public prior clearance'}
put('registry-check.json',reg)
print('built',len(rows),'dispositions; registry matches',reg)
