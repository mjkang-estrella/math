# Package Claude r602 lane payloads: dispositions.json, coverage.json, source-provenance.json, flat-bindings.json, failures.json.
# Inputs: assigned-records.json (bound), dispositions-input.json (judgments), fetch-log.tsv, derived-bindings.tsv. Usage: package.py BATCHDIR
import hashlib,json,os,sys
B=os.path.realpath(sys.argv[1]); LN=os.path.join(B,'lanes'); ME=os.path.join(LN,'claude-mathdb-primary-qualified-breadth-r602')
def h(p):
    s=hashlib.sha256(); n=0
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): s.update(b); n+=len(b)
    return s.hexdigest(),n
J=lambda p:json.load(open(p,encoding='utf-8'))
R=J(os.path.join(ME,'assigned-records.json')); DI=J(os.path.join(ME,'dispositions-input.json'))
ids=J(os.path.join(LN,'root-mathdb-breadth-intake-r601/reserved-ids.json'))['ids']
assert [x['mathdb_id'] for x in R]==ids and set(map(int,DI))==set(ids)
out=[]
for x in R:
    r=x['record']; d=DI[str(r['mathdb_id'])]
    can=json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8')
    st=r.get('statement') or ''
    assert hashlib.sha256(can).hexdigest()==x['canonical_record_sha256'] and hashlib.sha256(st.encode('utf-8')).hexdigest()==x['statement_utf8_sha256']
    out.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':'lanes/pi-mathdb-full-corpus-inventory-r301/'+x['chunk'],'line':x['line'],
      'line_sha256':x['line_sha256'],'canonical_record_sha256':x['canonical_record_sha256'],'statement_utf8_sha256':x['statement_utf8_sha256'],
      'statement':st,'title':r.get('title'),'source_url':r.get('source_url'),'mathdb_url':r.get('canonical_url'),
      'mathdb_statement_completeness_label':r.get('statement_completeness'),
      'statement_assessment':d['assessment'],'self_contained':d['assessment']=='self_contained','incomplete':d['assessment']=='incomplete',
      'scope_ambiguous':d['assessment']=='scope_ambiguous','definition_dependent':d['assessment']=='definition_dependent',
      'counted_as_complete_statement':d['assessment']=='self_contained','flags':d['flags'],'evidence_level':d['evidence_level'],
      'body_confirmed':False,'proof_audit':False,'registry':'HOLD: zero MathDB requests (inherited 429); current proof registry not consulted',
      'disposition':d['disposition'],'reason':d['reason'],'credit':0,'reviewer':'claude-mathdb-primary-qualified-breadth-r602'})
json.dump(out,open(os.path.join(ME,'dispositions.json'),'w',encoding='utf-8'),ensure_ascii=False,indent=1)
cnt={}
for o in out:
    for k in ('statement_assessment','evidence_level'):
        cnt.setdefault(k,{}); cnt[k][o[k]]=cnt[k].get(o[k],0)+1
    cnt.setdefault('disposition',{}); cnt['disposition'][o['disposition']]=cnt['disposition'].get(o['disposition'],0)+1
cov={'lane':'claude-mathdb-primary-qualified-breadth-r602','assignment_authority':'lanes/root-mathdb-breadth-intake-r601/reserved-ids.json',
 'current_authority':'lanes/root-mathdb-breadth-intake-r603','baseline_coverage_record_reviews':6033,'new_literal_record_reviews':len(out),
 'reviewed_ids':ids,'counts':cnt,'complete_statements_counted':sum(o['counted_as_complete_statement'] for o in out),
 'note':'Literal record reviews only; not complete-statement, body-confirmed or whole-corpus coverage. Abstract-level rows remain abstract-level.',
 'proposals':2,'credit':0}
json.dump(cov,open(os.path.join(ME,'coverage.json'),'w'),indent=1,sort_keys=True)
# provenance
fl=[l.rstrip('\n').split('\t') for l in open(os.path.join(ME,'fetch-log.tsv'),encoding='utf-8') if l.strip()]
dv=[l.rstrip('\n').split('\t') for l in open(os.path.join(ME,'derived-bindings.tsv'),encoding='utf-8') if l.strip()]
prov={'request_policy':'curl, single GET per URL, generic User-Agent "Mozilla/5.0 (X11; Linux x86_64) generic-research-fetch/1.0", no cookies/referer/credentials/personal data; https only; >=4s spacing for arXiv',
 'mathdb_requests':0,'parked_routes_touched':[],
 'fetches':[{'utc':a,'http':b,'sha256':c,'bytes':int(d),'url':e} for a,b,c,d,e in fl],
 'derivatives_bound_before_reading':[{'utc':a,'sha256':b,'bytes':int(c),'path':d} for a,b,c,d in dv],
 'body_coverage':{'1802.01952v2':'Sections 2 (definitions, Thm 2.1-2.2), 4.2 (Thm 4.3-4.6, Example 1, Conjecture 4.1) read; rest grep only',
   '1612.01128v1':'Section 4 (Conjecture 4.1, Prop 4.2, (B)-property discussion) read','1810.06820v2':'Section 1 (Problem 1-2, Conjecture 1, Omega, Theorems 1-2) read; proofs not read',
   '1806.03567v2':'Section 1.1 definitions and Section 4 (Question 4.1, Conjecture 4.2) read','1802.03754v1':'Section 1 (definitions, Thm 1.1-1.4, Conjecture 1.3) read',
   '2512.03968v2':'Intro pp.1-5 read; grep for BRT citation (none)','2607.27162v1':'Intro read; grep (no BRT)','2608.14232v1':'Section 1.1 examples read; grep (no BRT)',
   '2103.00941v2':'Intro, Section 4.2 text around Theorems 7-11, pages 39 and 43 rendered and viewed (Figures 29, 30, 35); adjacency not extracted',
   '1807.07253v1':'Abstract/intro, page 2 rendered (Figure 1, R1, R2: not regular)','1909.11565v1':'grep only','2305.07938v2':'grep only',
   'arxiv-api':'abstract metadata for all 48 source papers + 7 prior-art searches; abstract-level only'}}
json.dump(prov,open(os.path.join(ME,'source-provenance.json'),'w'),indent=1)
# flat bindings to originals (no copies)
FB=[]
def add(rel):
    s,n=h(os.path.join(B,rel)); FB.append({'path':rel,'sha256':s,'size':n})
for I in ('root-mathdb-breadth-intake-r601','root-mathdb-breadth-intake-r603'):
    for f in ('manifest.json','verification-receipt.json','reserved-ids.json','queue.json','active-breadth-reservations.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','bindings.json','routing-queue.jsonl','DECISION.md'):
        add('lanes/%s/%s'%(I,f))
m301=J(os.path.join(LN,'pi-mathdb-full-corpus-inventory-r301/manifest.json')); add('lanes/pi-mathdb-full-corpus-inventory-r301/manifest.json')
for e in [e for e in m301['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')]+m301['frozen_inputs']:
    add('lanes/pi-mathdb-full-corpus-inventory-r301/'+e['path'])
for f in ('root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md','root-mathdb-cayley-review-intake-r363/disposition.json','root-mathdb-cayley-review-intake-r363/reserved-ids.json','root-mathdb-banzhaf-retirement-intake-r503/reserved-ids-r504.json','sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'):
    add('lanes/'+f)
add('AGENTS.md'); add('../../../../AGENTS.md')
json.dump(FB,open(os.path.join(ME,'flat-bindings.json'),'w'),indent=1)
print(json.dumps({'dispositions':len(out),'flat_bindings':len(FB),'counts':cnt}))
