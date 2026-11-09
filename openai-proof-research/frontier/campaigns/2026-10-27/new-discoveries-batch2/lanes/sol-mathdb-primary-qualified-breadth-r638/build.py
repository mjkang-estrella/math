import pathlib,json,hashlib,collections
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r637'
def j(p):return json.loads(p.read_text())
def write(n,x):(P/n).write_text(json.dumps(x,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
lines=(P/'reviews.tsv').read_text().splitlines();rows={int(a[0]):a[1:] for a in (s.split('\t') for s in lines)}
rows[393284]=['incomplete','Primary: finite r-group R on finite r-prime-group G, with r prime; R abelian faithful, p>3, all alpha in R#','HOLD_SCOPE_SOURCE_COROLLARY','Exact primary Corollary I is proved under the standing coprime-action hypothesis (r prime, R an r-group, G an r-prime-group). Literal record omits it. Narrow intended assertion is old; broadened literal not settled here. Do not promote either as new.']
source={392991:('ems742.txt',259,317),393195:('ems784.txt',650,738),393200:('ems784.txt',1126,1162),393205:('ems784.txt',1670,1795),393206:('ems784.txt',1670,1795),393226:('ems787.txt',1762,1829),393270:('ems793.txt',231,305),393284:('ems793.txt',1465,1595),393285:('ems793.txt',1840,1895),393287:('ems793.txt',1975,2076),393362:('ems828.txt',800,910),393366:('ems828.txt',1890,1995),393367:('ems828.txt',1890,1995),393369:('ems828.txt',2390,2445),393371:('ems828.txt',2610,2642)}
passages=[]
for name,a,b in sorted(set(source.values())):
 s=(P/name).read_text().splitlines();passages.append(dict(file=name,start_line=a,end_line=b,text='\n'.join(s[a-1:b])))
write('selected-passages.json',passages)
ds=[]
for r in j(P/'literal-records.json'):
 i=r['mathdb_id'];cl,q,disp,why=rows[i];rec=r['record'];d={k:v for k,v in r.items() if k!='record'}
 d.update(statement_utf8=rec['statement'],source_url=rec['source_url'],source_version=rec['source_name'],quantifiers=q,flags=dict(complete=cl=='complete',incomplete=cl=='incomplete',definition_dependent=cl=='definition',scope_ambiguous=cl=='ambiguous'),reviewed_scope='literal statement technical screening; source gaps retained',disposition=disp,reason=why,accepted_credit=0,current_registry_cleared=False,full_scope_proof_established=False,source_coverage=dict(literal_record=True,selected_primary_passage=i in source,whole_primary_body=False,local_proof_body=(i==393226),full_dependency_audit=False,closest_prior_body=(i==393226),current_registry=False))
 if i in source:d['primary_passage']=source[i]
 if i==393226:d['prior_passage']=dict(file='0407108v1.txt',printed_pages='2-6',sections='1 and 1.1',coverage='resolution construction/exactness argument and image ranks read; cited Koszul facts and all remaining cases not audited',version_anomaly='URL/header v1 7 July2004; internal Date February8,2020. Retain exact bytes, do not infer chronology from internal date alone.')
 ds.append(d)
assert len(ds)==50 and set(rows)=={d['mathdb_id'] for d in ds};write('dispositions.json',ds);write('proposals.json',[])
write('source-coverage.json',dict(literal_records=50,flags=dict(collections.Counter(rows[i][0] for i in rows)),selected_primary_passage_records=len(source),whole_primary_bodies=0,local_proof_bodies=1,full_dependency_audits=0,current_registry_cleared=False,external_requests=dict(mathdb=0,ems_html=5,ems_pdf=5,arxiv_pdf=1),scope='Only selected text passages; diagrams, source images and formula layout not visually inspected; no image-based inference or whole-body clearance. Other 35 rows literal-only.'))
write('source-provenance.json',dict(primary_html=j(P/'fetch-provenance.json'),primary_pdf=j(P/'pdf-bindings.json'),text_derivatives=j(P/'derivative-bindings.json'),closest_prior=j(P/'prior-bindings.json'),closest_prior_derivative=j(P/'prior-derivative.json'),cached_corpus='Original r301 dated third-party mirror records; in-place references only',selected_passages='selected-passages.json',access='No MathDB/registry requests; inherited 429/unavailable HOLD. No search-hit absence inference. No blocked route retried.'))
# Read bounded relevant historical context only after its flat binding.
ctx=[]
for name in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 obj=j(L/name);matches=[]
 def walk(o):
  if isinstance(o,dict):
   if any(o.get(k) in rows for k in ['mathdb_id','related_mathdb_id']):matches.append(o)
   for v in o.values():walk(v)
  elif isinstance(o,list):
   for v in o:walk(v)
 walk(obj);ctx.append(dict(path=name,direct_id_matches=matches,limitation='Administrative family exclusions remain controlling; absence of direct ID matches does not clear novelty.'))
write('context-check.json',dict(context=ctx,counts=dict(additional=9,total=39,next=40),r363='Cayley364119 source-adaptation exclusion remains in force',current_adjudications=j(I/'adjudications.json'),hypothesis_queue=j(I/'hypothesis-queue.json')))
print(json.dumps(j(P/'source-coverage.json')))
