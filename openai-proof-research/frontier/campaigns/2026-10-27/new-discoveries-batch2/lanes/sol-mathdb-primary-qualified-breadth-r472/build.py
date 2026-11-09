import pathlib,json,hashlib,re,datetime
L=pathlib.Path(__file__).resolve().parent;B=L.parent;I=B/'root-mathdb-breadth-intake-r471'
j=lambda p:json.loads(p.read_text())
a={int(s.split('\t')[0]):s.rstrip('\n').split('\t')[1:] for s in (L/'assessment.tsv').read_text().splitlines()}
R=j(L/'assigned-records.json');assert len(a)==len(R)==50
sources=j(L/'retained-sources.json');loc=j(L/'located-passages.json');target=j(L/'target-locators.json');extra={e['source']:e for e in target}
for s in sources:
 p=L/'sources'/(s['arxiv_id']+'.txt')
 if p.exists():
  m=re.search(r'arXiv:'+re.escape(s['arxiv_id'])+r'v\d+[^\n]*',p.read_text());s['pdf_version_header']=m.group() if m else 'version header not extracted; HOLD'
 s['read_scope']='Selected passages only as logged in passages.log and target-passages.log; retained body is not a whole-body or dependency audit.'
(L/'retained-sources.json').write_text(json.dumps(sources,indent=2)+'\n')
checks=j(L/'bounded-checks.json')['checks'];out=[]
for e in R:
 r=e['record'];i=r['mathdb_id'];status,mechanism=a[i];s=r['source_url'].rsplit('/',1)[-1]
 out.append({'mathdb_id':i,'title':r['title'],'literal_statement':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode('utf-8')).hexdigest(),'canonical_record_sha256':e['canonical_record_sha256'],'canonical_record_encoding':'json.dumps(sort_keys=True,ensure_ascii=False,separators=(comma,colon)), UTF-8','original_chunk':e['chunk'],'original_line':e['line'],'source_url':r['source_url'],'record_url':r['canonical_url'],'disposition':status,'full_scope_mechanism_or_obstacle':mechanism,'evidence_levels':{'record':'full literal statement and quantifiers read','primary':'selected source passages inspected; '+('targeted ranges in target-locators.json' if s in extra else 'numbered conjecture/header excerpts in located-passages.json; definitions incomplete'),'source_internal_results':'only those explicitly identified in assessment; no complete theorem-body/dependency audit','closest_successors':'HOLD: no independent closest-successor search/body audit; cited source updates only','proof':'no new full-scope proof established','registry':'HOLD: zero MathDB requests under inherited 429; current public proof-registry clearance unavailable'},'primary_locator_files':['located-passages.json']+(['target-locators.json'] if s in extra else []),'whole_primary_body_read':False,'full_dependency_audit':False,'bounded_check':next((c for c in checks if c['id']==i),{'status':'not executed','reason':'No reliable full-scope small-certificate test selected; source/prior or deep mechanism gate remains'}),'prior_cleared':False,'accepted_credit':0})
(L/'dispositions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');(L/'proposals.json').write_text('[]\n')
res=j(I/'reserved-ids.json');cov=j(I/'coverage-delta.json');assert len(cov)==3133;assert set(a)==set(res['ids']);assert not set(a)&set(res['other_active_reservations']);assert not set(a)&set(map(int,cov));assert not set(a)&{372627,372628,368940,404067,364119}
# Read the complete association/exclusion tables as data, rather than trusting an upstream receipt.
ex=[]
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 p=B/'root-mathdb-accepted-exclusions-r304'/name;text=p.read_text();d=json.loads(text)
 hits=[i for i in a if re.search(r'(?<!\d)'+str(i)+r'(?!\d)',text)];assert not hits,(name,hits);ex.append({'path':str(p),'assigned_numeric_id_matches':hits,'bytes_read':len(text.encode())})
receipt={'status':'PASS','baseline_reported_statement_reviews':len(cov),'assigned':50,'exact_ids':res['ids'],'disjoint_other_active':True,'disjoint_prior_coverage':True,'accepted_and_historical_scan':ex,'counts_unchanged':{'additional':9,'total':39,'next':40},'credit':0,'note':'new 50 dispositions offered to root; no shared reconciliation performed'}
(L/'assignment-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('Built fifty dispositions, zero proposals;',len(sources),'source PDFs retained')
