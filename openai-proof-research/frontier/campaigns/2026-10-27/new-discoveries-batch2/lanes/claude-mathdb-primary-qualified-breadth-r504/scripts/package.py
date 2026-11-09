# Build lane payload JSONs from bound inputs. Writes only inside the lane directory given as argv[1].
import hashlib,json,os,sys,csv
L=os.path.realpath(sys.argv[1]); B=os.path.realpath(os.path.join(L,'../..')); LN=os.path.join(B,'lanes')
I=os.path.join(LN,'root-mathdb-banzhaf-retirement-intake-r503'); P=os.path.join(LN,'pi-mathdb-full-corpus-inventory-r301')
def h(p):
    s=hashlib.sha256(); n=0
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): s.update(b); n+=len(b)
    return s.hexdigest(),n
def dump(name,obj):
    with open(os.path.join(L,name),'w',encoding='utf-8') as f: json.dump(obj,f,ensure_ascii=False,indent=1,sort_keys=True); f.write('\n')
rec=json.load(open(os.path.join(L,'assigned-records.json'),encoding='utf-8'))
inp=json.load(open(os.path.join(L,'dispositions-input.json'),encoding='utf-8'))
ids=json.load(open(os.path.join(I,'reserved-ids-r504.json'),encoding='utf-8'))['ids']
assert [r['mathdb_id'] for r in rec]==ids
out=[]
for r in rec:
    d,ev,basis=inp[str(r['mathdb_id'])]; R=r['record']
    out.append({'mathdb_id':r['mathdb_id'],'title':R['title'],'canonical_url':R['canonical_url'],'post_type':R['post_type'],
      'source_url':R.get('source_url'),'corpus_chunk':r['chunk'],'corpus_line':r['line'],'corpus_line_sha256':r['line_sha256'],
      'canonical_record_sha256':r['canonical_record_sha256'],'statement_utf8_sha256':r['statement_utf8_sha256'],'statement':R['statement'],
      'literal_statement_read':True,'disposition':d,'evidence_level':ev,'basis':basis,'credit':0,
      'novelty_or_math_pass':False})
dump('dispositions.json',out)
dump('proposals.json',[])
from collections import Counter
dump('coverage.json',{'lane':'claude-mathdb-primary-qualified-breadth-r504','literal_statement_reviews':50,'ids':ids,
 'disposition_counts':dict(Counter(x['disposition'] for x in out)),'evidence_level_counts':dict(Counter(x['evidence_level'] for x in out)),
 'primary_body_passages_read':['406512 (arXiv:2610.20135v1 lines 1-30,60-175,720-737 of derived text)'],
 'third_party_pages_read':['383714 OEIS A080170','405261 erdosproblems.com/848'],
 'proof_bodies_audited':0,'current_registry_checked':False,'proposals':0,
 'note':'50 literal statement reviews. Not proof audits, not novelty clearance, not registry clearance. Abstract-level retirements are not body-level clearance.'})
# flat bindings of originals
fl=[]
for p in ['manifest.json','queue-r504.json','reserved-ids-r504.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','verification-receipt.json','active-breadth-reservations.json','bindings.json','coverage-summary.json','DECISION.md','frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json']:
    fl.append(os.path.join(I,p))
m301=json.load(open(os.path.join(P,'manifest.json'),encoding='utf-8'))
fl.append(os.path.join(P,'manifest.json'))
fl+= [os.path.join(P,e['path']) for e in m301['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')]
fl+= [os.path.join(P,e['path']) for e in m301['frozen_inputs']]
for p in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md','root-mathdb-cayley-review-intake-r363/disposition.json','root-mathdb-cayley-review-intake-r363/reserved-ids.json','sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
    fl.append(os.path.join(LN,p))
dump('flat-bindings.json',[{'original':p,'sha256':h(p)[0],'size':h(p)[1]} for p in fl])
# provenance
rows=[l.rstrip('\n').split('\t') for l in open(os.path.join(L,'fetch-log.tsv'),encoding='utf-8')]
fetch=[{'utc':a,'http_and_bytes':b,'sha256':c,'size':int(d),'url':e} for a,b,c,d,e in rows]
der=[dict(zip(['sha256','size','path'],l.rstrip('\n').split('\t'))) for l in open(os.path.join(L,'derived-bindings.tsv'),encoding='utf-8')]
dump('source-provenance.json',{'fetches':fetch,'fetch_local_files':{'https://export.arxiv.org/api/query?id_list=2605.25264,...':'fetched/arxiv-api/batch1.xml'},
 'derived_bindings_bound_before_reading':der,'access':{'mathdb_requests':0,'github_requests':0,'google_requests':0,'browser':False,'blocked_or_challenge_responses':0,
  'note':'arXiv export API x3, arXiv PDF x1, OEIS x2, erdosproblems x1; all HTTP 200. The OEIS HTML includes a Cloudflare JS beacon; the content was served directly and was not a challenge page.'},
 'not_fetched':['Zenodo 10.5281/zenodo.22660798 (405372)','GitHub sources 405261/383338/383181/383714/406237 (restricted route)','ProofAtlas pages','Sawhney note (405261)','all other PDFs; only arXiv:2610.20135v1 body read'],
 'pdf_extraction':'pdftotext -layout on bound PDF; output bound in derived-bindings.tsv before grep/read'})
fails=[dict(zip(['id','utc','description'],l.rstrip('\n').split('\t'))) for l in open(os.path.join(L,'failures.tsv'),encoding='utf-8')][1:]
dump('failures.json',fails)
print('ok',len(out))
