import json,pathlib,hashlib,datetime,collections
W=pathlib.Path(__file__).resolve().parent;L=W.parent;B=L.parent
J=lambda p:json.loads(p.read_text())
H=lambda b:hashlib.sha256(b).hexdigest()
extra=[]
for p in [B/'ledger.json',B/'prior-campaign-context.json',L.parents[3]/'AGENTS.md',B/'AGENTS.md']:
 if p.is_file():extra.append({'path':str(p),'sha256':H(p.read_bytes()),'size':p.stat().st_size,'timing':'supplemental administrative reference; not claimed pre-read'})
(W/'supplemental-bindings.json').write_text(json.dumps(extra,indent=2)+'\n')
a=J(W/'assigned-records.json'); assessments={int(t[0]):t[1:] for s in (W/'assessments.tsv').read_text().splitlines() if (t:=s.split('\t',3))}
assert len(assessments)==50
ex=J(W/'frozen/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json');hist=J(W/'frozen/root-mathdb-accepted-exclusions-r304/historical-dispositions.json')
res=[]
for x in a:
 r=x['record'];id=r['mathdb_id'];d,loc,note=assessments[id];src=r['source_url'].split('/')[-1];p=W/'sources'/(src+'.pdf');t=p.with_suffix('.txt')
 matches=[]
 for k,entries in hist.items():
  if isinstance(entries,list):
   for e in entries:
    if isinstance(e,dict) and (e.get('mathdb_id')==id or id in e.get('mathdb_ids',[])):matches.append({'section':k,'entry':e})
 res.append({'mathdb_id':id,'original_literal_statement':r['statement'],'original_chunk':x['original_chunk'],'original_line':x['original_line'],'statement_utf8_sha256':H(r['statement'].encode()),'canonical_record_sha256':H(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'primary_url':r['source_url'],'canonical_url':r['canonical_url'],'disposition':d,'technical_disposition':note,'primary_locator':loc,'source_pdf':str(p),'source_pdf_sha256':H(p.read_bytes()),'source_text':str(t),'source_text_sha256':H(t.read_bytes()),'evidence_levels':{'literal_statement':'all quantifiers read','primary':'selected passages only; target/nearby results, not whole-body audit','primary_definitions':'partial; missing global dependencies are not inferred','proof':'endpoint proof passage read' if id in [342547,343375,343510,343511,343748,344153] else 'no complete proof-body coverage claimed','dependency':'published dependencies not independently replayed','successor':'1910.06958 Theorem7.16 and proof read' if id==343748 else '2501.04953 selected statement/restriction passages read' if id in [343319,343320] else 'incomplete; source-internal reports distinguished','registry':'HOLD current registry not cleared; zero MathDB requests; inherited 429'},'duplicate_prior_status':'identified published endpoint or source-reported prior; see technical disposition' if d.startswith('RETIRE') else 'not cleared; no novelty inference','exclusion_check':{'accepted_lookup':ex.get('mathdb_lookup',{}).get(str(id)),'historical_matches':matches,'r481_372627_excluded':True,'r363_364119_excluded':True,'forbidden_ids_not_investigated':[372627,372628,368940,404067,364119]},'accepted_credit':0,'qualified_brief':False})
assert {r['mathdb_id'] for r in res}==set(assessments)
(W/'dispositions.json').write_text(json.dumps(res,ensure_ascii=False,indent=2)+'\n');(W/'proposals.json').write_text('[]\n')
counts=collections.Counter(r['disposition'] for r in res)
coverage={'baseline_reported_literal_reviews':3333,'own_new_literal_reviews':50,'baseline_plus_own_only':3383,'concurrent_reviews_not_reconciled':True,'primary_pdfs_retained':45,'successor_pdfs_retained':2,'literal_statements_read':50,'primary_coverage':'selected passages; no whole-body coverage claimed','whole_bodies_read':0,'endpoint_proof_passages_read_ids':[342547,343375,343510,343511,343748,344153],'complete_dependency_audits':0,'current_registries_cleared':0,'qualified_briefs':0,'accepted_credit':0,'campaign_counts':{'additional':9,'total':39,'next':40},'disposition_counts':dict(counts),'registry_status':'HOLD','requests_to_mathdb':0}
(W/'coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
(W/'search-provenance.json').write_text(json.dumps({'date':'2026-10-31','tool':'web.run search_query','queries':['planar homomorphism counts quantum isomorphism Mančinska Roberson arxiv','generalized Lyndon words conjecture every finite prefix infinite solved','subcubic injective edge coloring six five conjecture proof arxiv','probabilistic zero forcing throttling trees square root conjecture proved'],'primary_leads_retained':['https://arxiv.org/abs/1910.06958','https://arxiv.org/abs/2501.04953'],'limits':'Search snippets are discovery leads only. No direct Google route, GitHub route, ScienceDirect, ResearchGate or browser accessed. No claim of exhaustive successor search or current registry clearance.'},indent=2)+'\n')
print('built',len(res),dict(counts))
