import os, resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
resource.setrlimit(resource.RLIMIT_AS, (6*1024**3, 6*1024**3))
from pathlib import Path
import json, hashlib, base64, re, collections, datetime, shutil, ast
P=Path(__file__).resolve().parent.parent
ROOT=P/'root-intake-r60'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def digest(b): return hashlib.sha256(b).hexdigest()
def save(p,v):
    assert not p.exists(), str(p)
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==55
chunks={}; summaries=[]
for tag,mname,terminal in [('r432','MANIFEST.json','terminal_manifest.receipt.json'),('r433','SHA256-MANIFEST.json','manifest_terminal.receipt.json')]:
    a=P/('expanded-corpus-'+tag)
    manifest=json.loads((a/mname).read_text()); rows=manifest['files']
    assert isinstance(rows,list)
    bad=[r['path'] for r in rows if sha(a/r['path'])!=r['sha256']]
    assert not bad,bad
    frozen=json.loads((a/'frozen-inputs.json').read_text())
    assert all(sha(Path(s))==v for s,v in frozen.items())
    reserve=json.loads((a/'reservation.json').read_text());ids=reserve['ids']
    assert len(ids)==20 and len(set(ids))==20
    assert (a/'reservation.sha256').read_text().split()[0]==sha(a/'reservation.json')
    prov=json.loads((a/'literal-provenance.json').read_text());assert len(prov)==20
    proven=[]
    for row in prov:
        cid=Path(row.get('chunk_path',row.get('chunk')))
        if str(cid) not in chunks:
            b=cid.read_bytes();chunks[str(cid)]=(digest(b),b.splitlines(keepends=True))
        ch,lines=chunks[str(cid)];assert ch==row['chunk_sha256']
        raw=lines[row.get('one_based_line',row.get('line'))-1]
        assert raw.endswith(b'\n') and digest(raw)==row.get('raw_line_sha256',row.get('raw_sha256'))
        if 'raw_line_base64' in row: assert base64.b64decode(row['raw_line_base64'])==raw
        else: assert (a/'literals'/f"{row['id']}.jsonl").read_bytes()==raw
        obj=json.loads(raw); assert obj['mathdb_id']==row['id']
        token=re.search(rb'"statement"\s*:\s*("(?:\\.|[^"\\])*")',raw).group(1)
        assert digest(token)==row.get('raw_statement_token_sha256',row.get('statement_token_sha256'))
        assert json.loads(token)==obj['statement']
        assert digest(obj['statement'].encode())==row.get('decoded_statement_sha256',row.get('statement_utf8_sha256'))
        proven.append(row['id'])
    assert set(proven)==set(ids)
    if tag=='r433':
        aggregate=(a/'original-fixed20.jsonl').read_bytes().splitlines(keepends=True)
        assert len(aggregate)==20 and {json.loads(x)['mathdb_id'] for x in aggregate}==set(ids)
        assert all(base64.b64decode(row['raw_line_base64']) in aggregate for row in prov)
    gates=json.loads((a/'results.json').read_text());assert set(map(int,gates))==set(ids)
    previous='0'*64;events=[]
    for i,line in enumerate((a/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
        event=json.loads(line);assert event['seq']==i and event['previous']==previous
        previous=digest(line);events.append(event)
        if event['event']=='success': assert sha(a/event['destination'])==event['sha256']
    recs=[]
    for r in rows:
        if r['path'].endswith('.receipt.json'):
            v=json.loads((a/r['path']).read_text());recs.append({'path':r['path'],'exit':v.get('exit'),'killed':v.get('killed'),'sha256':r['sha256']})
    v=json.loads((a/terminal).read_text());recs.append({'path':terminal,'exit':v.get('exit'),'killed':v.get('killed'),'sha256':sha(a/terminal)})
    if tag=='r432': response_names=[f'search{i}-response.json' for i in [1,2,3]]
    else: response_names=[f'search{i}-full-response.json' for i in [1,2,3]]
    responses=[{'path':name,'type':type(json.loads((a/name).read_text())).__name__,'sha256':sha(a/name)} for name in response_names]
    budget=json.loads((a/'search-budget.json').read_text())
    assert budget['calls_used']==3 and budget['queries_used']==9
    after=json.loads((a/'frozen-after.json').read_text());assert after['count']==12 and not after['mismatches']
    inv=json.loads((a/'access-inventory.json').read_text())
    record={'utc':now,'lane':str(a),'accepted_new':55,'target_new':60,'previous_accepted':39,'credit':0,'root_execution':'Documentary integrity/orchestration only; no mathematical program or Lean execution',
      'manifest':{'path':str(a/mname),'sha256':sha(a/mname),'files_verified':len(rows),'mismatches':[],'terminal_exclusions':manifest.get('terminal_noncircular_self_exclusions')},
      'frozen_bindings_verified':len(frozen),'frozen_mismatches':[],'frozen_after':after,
      'literal_bindings_verified':proven,'reservation_sha256':sha(a/'reservation.json'),'raw_tokens_and_decoded_statements_verified':True,
      'guard_chain_verified':True,'guard_chain_last_sha256':previous,'get_event_counts':dict(collections.Counter(x['event'] for x in events)),
      'unavailable_guard_events':[x for x in events if x['event']=='unavailable'],'author_access_inventory':inv,
      'receipt_count':len(recs),'receipt_exit_counts':dict(collections.Counter(str(x['exit']) for x in recs)),'receipts':recs,
      'search_calls':3,'search_query_strings':9,'full_search_responses':responses,
      'all20_author_gates':gates,'root_disposition':'No acceptance. Full ordinary proposals require independent scope/proof/prior/significance reviews; source corrections/known results remain zero-credit.',
      'procedural_limits':('Late broad source-family reconciliation for cover/MIS remains a historical HOLD; earlier exact-ID check does not retroactively pay it. Failed GET preserved; registry metadata not body clearance; native/writer and sampling limits retained.' if tag=='r432' else 'Search1 counter typo corrected BEFORE actual call, both receipts preserved. Apparent MathDB200 carries challenge script; artifact unavailable, no guard-ledger rewrite. Conflicting banner/body edition dates are not silently resolved. Failed403 and sampling/native/writer limits retained.'),
      'ordinary_proposals_pending':([323059,323064,323065,323710] if tag=='r432' else [324571]),
      'new_reviews_planned':([323059,323710] if tag=='r432' else [324571]),
      'source_or_prior_gaps_not_retrieval_permissions':True}
    save(P/f'expanded-corpus-{tag}-parent-integration.json',record)
    summaries.append({'lane':str(a),'manifest_files':len(rows),'frozen':len(frozen),'literal_bindings':len(proven),'receipt_count':len(recs),'exit_counts':record['receipt_exit_counts'],'get_event_counts':record['get_event_counts']})

old=ROOT/'inherited-denials-cmdrr-review-r1.json';den=json.loads(old.read_text());den['utc']=now
add=[('https://www.mscand.dk/article/download/18001/15760/41028','Chapoton Mathematica Scandinavica115(2014)20-61 final flows-on-rooted-trees work',404,P/'expanded-corpus-r432/guard-ledger.jsonl'),
 ('https://www.sciencedirect.com/science/article/am/pii/S0097316519301177','P-partition generating function equivalence of naturally labeled posets, PII S0097316519301177',403,P/'expanded-corpus-r433/guard-ledger.jsonl'),
 ('https://mathdb.com/p/324571/equal-distribution-pair-discrepancy-bound','Current MathDB324571 record delivery containing challenge-platform script',200,P/'expanded-corpus-r433/access-inventory.json')]
for url,artifact,status,evidence in add:
    key=url.split('://',1)[-1];den['blocked_keys']=sorted(set(den['blocked_keys']+[key]))
    den['blocked_artifacts']=sorted(set(den['blocked_artifacts']+[artifact.lower()]))
    den['records'].append({'url':url,'reason':{'status':status,'artifact':artifact,'body_clearance':False,'classification':'Challenge suffix despite transport200, no script followed/no ledger backfill' if status==200 else 'Unavailable before primary body, all alternate deliveries forbidden'},'evidence':{'path':str(evidence),'sha256':sha(evidence)}})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts']+['s0097316519301177']))
den['root_r432_r433_scope']='Chapoton2014final and identified P-partition accepted2019work are artifact-wide unavailable after404/403: no alternatehosts/query/versions/arxiv/cache/mirror/DOI/author delivery. Already saved DISTINCT original flow1203.1780 and posets1210.2412 only copied/authorized. Specific Su2017 fork paper remains UNREAD but was not denied; no title-only theorem clearance. Current MathDB324571 delivered challenge suffix, all alternate record delivery unavailable; saved immutable corpus literal and actual1211.6486original/final2015article are distinct authorized cached bodies. Never backfill old transport-success ledger.'
denpath=ROOT/'inherited-denials-r433-intake.json';save(denpath,den)

# Reuse ONLY the plain instruction constant, not execution of old prep script.
tree=ast.parse((ROOT/'prepare-two-reviews-20261108.py').read_text())
common=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='COMMON' for t in n.targets))
common=common.replace('Inherited denial union r432','Inherited latest denial union r433-intake')
common=common.replace("routes ['TARGET']",'routes containing EVERY actually affected reserved ID string (one target per artifact unless shared)')
common+='\nExplicit skill access exception: reading the available PDF SKILL.md via runner is allowed for this read-only review. Direct image display of OWN rendered documentary images is allowed as UI evidence; do not misreport its unavailable process telemetry. No PDF authoring marker for read-only rendering. All other paths must be own copied inputs or approved skills; no embedded external proof/source paths.\n'

shoe_detail='''FULL independent review324571, not numerical checking. Read actual copied original1211.6486v2 and finalAAP47(2015)292-305 DOI10.1239/aap/1427814592, Sections2-4/9.1-9.2 including Conjecture4 eq19, whole relevant Theorem3 proof and all standing hypotheses. The source rule is STRICT ALTERNATION L1,R1,L2,R2,..., not simultaneous pairs or independent Poisson clocks. All discrete distributions, including countably infinite support, zeros/point masses. Author proposes D(p,p)<=255/256 via pointwise minorization y_i>=x_i/256 with x_i=p_i^2/s, s=sum p_i^2. Independently verify first-match law, almost-sure termination using (1-s)^N, exact chronological uniqueness and tie handling, conditional product events E_ab, finite union bound for NON-i cross matches, Bernoulli/floor estimates, countable sum/TV identity, and strict SUPREMUM rather than merely each-law D<1. Full author proof is untrusted; try adversarial edge cases personally, no mathematical program. Repair any actual gap or isolate precise GAP, do not import author conclusions as lemmas.
Large s>=1/64 uses first pair; small s K=floor(1/(4sqrt(s))) has K>=1/(8sqrt(s)), K^2s<=1/16; events exactly one i each side among K draws have probability p_i^2(1-p_i)^(2K-2), disjoint over K^2pairs. Conditional any other-color cross match probability <=(K-1)^2s/(1-p_i)^2<=4/49<1/2; each surviving event forces chronological first color i, regardless of arrival order. Bernoulli gives power>=1/2; sum then>=p_i^2/(256s). Check every direction, no hidden conditioning/earlier match outside block.
Source-final scope was read for material passages, figures4-5 not used; independently inspect any material definition/figure and separate visual claims. No refetch cached original/final, roots or denied MathDB record. The MathDB200challenge suffix does not affect cached literal provenance or actual journal PDF. Current root metadata do not clear relevant proof bodies. Use at most2 targeted searches/6queries and8 guarded GET-hops to identify ACTUAL applicable general collision/minorization or birthday-sampling primary results, any later exact bound/correction, and current registry counterparts, then read actual theorem/proof if found. A general minorization theorem requires full applicable bridge with independence/alternation/countable-law/constant hypotheses paid. No worldwide novelty claim from nonmatches.
FOR significance: uniform dimension-free constant answering exact equal-marginal final conjecture, not finite-support compactness or special limiting family. AGAINST: elementary birthday-block/union bound might be known as a general collision-sampling theorem. Shortness or probability-tool familiarity alone is not exclusion; complete prior bridge and strongest contrary case needed. Compare supplied55+39 full scopes personally before investment, no certificate reaudit. If prospective scientific PASS, dormant full literal Lean construction including infinite probability space/stopping law/TV bridges, no implementation or dispatch. Credit0. Final all gates separate with independent full proof/GAP and exact prior/source/access limits.'''
graph_detail='''Independently review TWO distinct candidate endpoints323710 and323059; no shared-family presumption merely because both are graphs. Read ALL their exact literals and supplied author proposals and actual primary definitions/standing hypotheses before substantial proof investment. The author's early source-family reconciliation was late for both; preserve that historical process HOLD, perform your OWN supplied94scope comparison before investment instead of retroactively declaring author compliance.
323710: actual1206.6605v1 A Tractable Variant of Cover Time, Definition1.1/equation1/Conjecture5.4, companion1302.3212v2 and author publication page/current version metadata already copied. Source cc_r=(1/(|V|-1))sum_v H_r(v), CT first visit all vertices WITHOUT return. Fixed vertex count320, endpoint-rooted path has ratio (n+1)(2n+1)/(6n^2)<3/8 at n319. Candidate path length64 attached to K256 at its endpoint, root other end (320 total) allegedly has cc/CT>3/7. Audit first-step equations/finiteness/uniqueness, path H0(v)=L^2, all cliquepointsH>=L^2, embedded-clique suppression of tail excursions, return duration2L-1 and expected transition duration1+2L/(m-1), conditional uniform neighbor/history, coupon-stage (m-1)/k, optional-summing/tower stopping with finite expectations, upper CT<=L^2+(m-1+2L)H255, eight dyadic-block boundH255<=8, all exact arithmetic. No altered normalization, resolvent, roundtrip cover or vertex count. Investigate actual final/current source/correction and specific companion result that could subsume the ratio; don't treat clique-star centrality-ordering example as exact target without full bridge. Assess whether familiar lollipop+coupon structure supplies a complete applicable prior reduction or substantive missing content; full strongest contrary case.
323059: actualIlinca-Kahn1202.4427v1 Section5Conjecture5.2/preceding hypotheses and history page copied. Literal d=8,n=36, d congruent2mod3 and2(d-2)=12 divides36; four disjoint K9. Explicit bijection maximal independent sets to four vertex choices gives9^4=3^8>2^3*3^6. Independently check connectedness/not-a-clique/additional degree thresholds or standing hypotheses, source final/correction/exponent transcription, the d=8 extremal triangle construction and scope. d=2singularity correction is NOT this witness. d->infinity asymptotic theorem not immediate contradiction. Obtain applicable actual primary current/final/prior bodies where independently identified, no theorem exclusion from snippets alone. Do not call smallness alone routine; if source typo/range correction, explicitly classify it at zero. Author had no late-route native search budget, so source/current prior review is essential.
Budget focused across BOTH: at most2actualsearchcalls6querystrings and8TOTAL GET-HOPS (perID<=8), all redirects precharged. Persist exact single plan/routes for actual affectedID, shared artifact BOTH if relevant. No cached refetch. Read full applicable theorem AND proof; strongest contrary significance case and source final/version gate for each separately. All mathematical work personally without programs. Bound current nonmatches not worldwide novelty; concrete matching unread theorem preciseHOLD. If both prospective PASS, separate dormant full-literal Lean obligations only, no implementation. Read shared author FULLCANDIDATE scoring sections only for context if needed, but323064/323065 are NOT review targets; they remain parked/uncredited separately. Return separate keyed gates and full independent proofs/GAPs.'''
specs=[{'lane':'shoe-pair-discrepancy-source-review-sol-r1','author':'expanded-corpus-r433','ids':[324571],'detail':shoe_detail,
 'files':['ACTUALBRIEF.md','FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','literal-provenance.json','original-fixed20.jsonl','results.json','prior-reconciliation.json','history-assessment.json','access-inventory.json','read-inventory.json','registry-inventory.json','resource-inventory.json','SHA256-MANIFEST.json','search1-full-response.json','search2-full-response.json','search3-full-response.json'],
 'sources':['shoes.pdf','shoes.txt','shoes-final.pdf','shoes-final.txt']},
 {'lane':'cover-ratio-regular-mis-source-review-sol-r1','author':'expanded-corpus-r432','ids':[323710,323059],'detail':graph_detail,
 'files':['ACTUALBRIEF.md','FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','literal-provenance.json','results.json','early-history-audit.json','family-reconciliation.json','access-inventory.json','source-read-inventory.json','registry-navigation.json','resource-inventory.json','MANIFEST.json','search1-response.json','search2-response.json','search3-response.json'],
 'sources':['cover.pdf','cover.txt','cover-companion.pdf','cover-companion.txt','cover-author.html','mis.pdf','mis.txt','mis-history.html','current-openai-contents.md','current-leanpool-index.txt','current-tau-index.txt','current-deepmind-proofs.md']}]
base=P/'expanded-corpus-r420';prepared=[]
for spec in specs:
    lane=P/spec['lane'];a=P/spec['author'];assert not lane.exists();lane.mkdir();origins={}
    def cp(src,rel):
        dst=lane/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst)
        origins[rel]={'path':str(src),'sha256':sha(src)}
    for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:cp(base/name,name)
    cp(denpath,'inherited-denials.json')
    for name in spec['files']:cp(a/name,'inputs/'+name)
    for name in spec['sources']:cp(a/'sources'/name,'inputs/sources/'+name)
    if spec['author'].endswith('r433'):
        for name in ['registry-openai.html','registry-leanpool.html','registry-tau.html','registry-deepmind.html']:cp(a/'sources'/name,'inputs/sources/'+name)
    for target in spec['ids']:
        if spec['author'].endswith('r432'):cp(a/'literals'/f'{target}.jsonl',f'inputs/literal{target}.jsonl')
        else:
            raw=next(x for x in (a/'original-fixed20.jsonl').read_bytes().splitlines(keepends=True) if json.loads(x)['mathdb_id']==target)
            q=lane/f'inputs/literal{target}.jsonl';q.write_bytes(raw);origins[str(q.relative_to(lane))]={'path':str(a/'original-fixed20.jsonl'),'aggregate_sha256':sha(a/'original-fixed20.jsonl'),'sha256':digest(raw),'extraction':'Unchanged complete newline JSONL object'}
    cp(ROOT/'accepted55-path-review-context.json','inputs/accepted55-routing.json')
    cp(P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json','inputs/prior39-routing.json')
    cp(P/(spec['author']+'-parent-integration.json'),'inputs/ROOT-AUTHOR-INTEGRATION.json')
    save(lane/'INPUT-ORIGINS.json',origins)
    save(lane/'reservation.json',{'ids':spec['ids'],'role':'Independent ordinary/source/final/current-prior/significance review; no formal execution','author_lane':str(a),'accepted_new':55,'target_new':60,'credit':0})
    rs=sha(lane/'reservation.json');(lane/'reservation.sha256').write_text(rs+'  reservation.json\n')
    save(lane/'search-budget.json',{'calls_used':0,'queries_used':0,'maximum_calls':2,'maximum_queries':6,'charged_before_call':True})
    peers=['cmdrr-five-three-formal-sol-r2']+[s['lane'] for s in specs if s['lane']!=spec['lane']]
    task='Independent review targets '+str(spec['ids'])+' in '+str(lane)+'. Reservation SHA256 '+rs+'.\nPROTECTED ACTIVE/PLANNED peers '+', '.join(peers)+': no read/hash/glob/list/poll even metadata.\n'+common.replace('LANE',str(lane))+'\nSPECIFIC SCOPE:\n'+spec['detail']
    (lane/'TASK.txt').write_text(task)
    frozen={str(q):sha(q) for q in a.rglob('*') if q.is_file()}
    frozen.update({str(q):sha(q) for q in (lane/'inputs').rglob('*') if q.is_file()})
    for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','inherited-denials.json','INPUT-ORIGINS.json','reservation.json','reservation.sha256','TASK.txt']:frozen[str(lane/name)]=sha(lane/name)
    assert all(sha(Path(s))==v for s,v in frozen.items())
    save(lane/'frozen-inputs.json',frozen)
    save(lane/'ROOT-PREP.json',{'utc':now,'lane':str(lane),'author':str(a),'ids':spec['ids'],'frozen_count':len(frozen),'reservation_sha256':rs,'task_sha256':sha(lane/'TASK.txt'),'accepted_new':55,'credit':0,'protected_peers':peers,'model':'gpt-6.1-sol','reasoning_effort':'high','service_tier':'default','children':False,'budgets':{'GET_hops_total':8,'search_calls':2,'querystrings':6}})
    prepared.append({'lane':str(lane),'ids':spec['ids'],'frozen_count':len(frozen),'task_sha256':sha(lane/'TASK.txt')})
save(ROOT/'r432-r433-intake-and-review-ready.json',{'utc':now,'intakes':summaries,'prepared':prepared,'latest_denial_union':str(denpath),'accepted_new':55,'credit':0,'active_formal_lane':'cmdrr-five-three-formal-sol-r2','root_role':'Documentary orchestration only'})
print(json.dumps({'intakes':summaries,'ready_reviews':prepared}))
