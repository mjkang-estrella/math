import pathlib,json,hashlib,math,datetime,collections,subprocess
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r695'
load=lambda p:json.loads(p.read_text())
def write(n,d):(O/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def bind(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
# Exact bounded endpoint check, not a scientific discovery.
s=1;q=qt=1;p=[0,0,1];sums=[sum(math.comb(s-1+k-m,s-1)*p[m]*q**m*(-qt)**(k-m) for m in range(min(k,s)+1)) for k in range(s+2)];assert sums==[0,0,0] and p[2]!=0
write('bounded-checks.json',{'executed':True,'method':'exact Python integers','mathdb_id':325243,'s':s,'q':q,'qtilde':qt,'p':p,'hypothesis_sums':sums,'forced_p2':0,'actual_p2':1,'credit':0,'interpretation':'unconstrained-coordinate wording defect only; no repaired theorem'})
A={}
for line in (O/'assessments.tsv').read_text().splitlines():
 id,cl,qu,reason,status,tech=line.split('\t');A[int(id)]=(cl,qu,reason,status,tech)
records=load(O/'literal-records.json');assert len(A)==50 and set(A)=={x['record']['mathdb_id'] for x in records}
D=[]
for x in records:
 r=x['record'];id=r['mathdb_id'];cl,qu,reason,status,tech=A[id]
 D.append(dict(mathdb_id=id,title=r['title'],statement=r['statement'],statement_utf8_sha256=hashlib.sha256(r['statement'].encode()).hexdigest(),canonical_record_sha256=x['canonical_record_sha256'],corpus_chunk=x['chunk'],corpus_line=x['line'],corpus_line_sha256=x['line_sha256'],classification=cl,classification_reason=reason,quantifiers=qu,disposition=status,technical_assessment=tech,source_url=r['source_url'],evidence={'literal_statement':'read in full','selected_primary_passage':id in [320721,325243],'whole_primary_body':False,'local_proof': 'exact unconstrained-coordinate check only' if id==325243 else 'not established independently','full_dependency_audit':False,'successor_body_review':False,'current_registry':'HOLD unavailable; no requests or absence inference'},accepted_credit=0,novelty_cleared=False))
write('dispositions.json',D);write('proposals.json',[])
flat=load(O/'initial-bindings.json')['files'];flat += [bind(L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')]
for pth in [L/'sol-mathdb-primary-qualified-breadth-r692/failures.json']:
 flat.append(bind(pth))
# bind required frozen stopped-route references without expanding historical trees
for suffix in ['r578','r642','r684']:
 for lane in L.glob('*'+suffix):
  for name in ['failures.json','source-provenance.json']:
   pth=lane/name
   if pth.is_file():flat.append(bind(pth))
write('flat-bindings.json',list({e['path']:e for e in flat}.values()))
# Select only bounded primary excerpts, not entire bodies.
passages=[]
for id,ranges in [(320721,[(100,150)]),(325243,[(629,650)])]:
 pth=O/(str(id)+'.txt');lines=pth.read_text().splitlines()
 for lo,hi in ranges:passages.append({'mathdb_id':id,'text_file':str(pth),'first_line':lo,'last_line':hi,'text':'\n'.join(lines[lo-1:hi]),'scope':'selected primary question/theorem/reduction only; whole body and dependencies unread'})
write('selected-passages.json',passages)
write('source-coverage.json',{'records':50,'classification_counts':dict(collections.Counter(d['classification'] for d in D)),'selected_primary_ids':[320721,325243],'whole_body_reviews':0,'independent_full_dependency_reviews':0,'successor_body_reviews':0,'registry':'HOLD unavailable','mathdb_requests':0,'http_requests':2,'no_proposals_reason':'No eligible full-scope new mechanism survives scope, known primary exception, wording-defect and source/prior gates.'})
write('failures.json',{'new_fetch_failures':[],'stopped_routes_preserved':['MathDB 429: zero requests','r578 failures: preserve bound original failures file; no retry','r642 author Gorenstein PDF TLS failure: no retry','r684 two arXiv v2 404 fetches: no retry','OEIS A274199/internal r542 HTTP403: no retry or alternate route','DOI10.1093/imrn/rnz305 academic.oup.com r618 HTTP403 Cloudflare: no retry or alternate route','AIM/Kourovka/EGRES/AIProofWatch parked','DMGT TLS; ProjectEuclid challenge; ResearchGate403 parked'],'registry':'unavailable => HOLD','338366':'Excluded from credit: published object reconstructed with text/figure defects; journal bodies unread. Not reopened.','deviations':['No upstream verify.py executed. No corpus copied. No mathematical novelty clearance. No successor body clearance: no hypothesis promoted.'],'negative_test_failures':[]})
print('classification',collections.Counter(d['classification'] for d in D))
# Page index for visual check of critical formula; hash image before viewing.
pdf=O/'325243.pdf';pages=(O/'325243.txt').read_text().split('\f');page=next(n for n,t in enumerate(pages,1) if 'Conjecture 2.11. Fix' in t)
subprocess.run(['pdftoppm','-f',str(page),'-l',str(page),'-scale-to','1500','-singlefile','-png',str(pdf),str(O/'325243-question')],check=True)
write('visual-binding.json',{'pdf':bind(pdf),'page':page,'image':bind(O/'325243-question.png')})
print('visual page',page)
