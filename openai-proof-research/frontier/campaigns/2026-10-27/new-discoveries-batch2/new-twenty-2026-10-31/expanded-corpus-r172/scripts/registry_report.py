import pathlib,json,hashlib,re,datetime,urllib.parse
D=pathlib.Path(__file__).resolve().parents[1];rows=json.loads((D/'extracted.json').read_text());report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'registries':{},'github_search':[],'targets':{},'limitations':['A path screen is not proof-body review. No external Lean development was replayed. Repository search is metadata search, not code search.','Root recursive trees were truncated for Omega and OpenAI; complete D5/Problems and preprints scopes were obtained separately. Other scopes remain incomplete.']}
for repo in ['Vilin97/lean-pool','the-omega-institute/trureturing','openai/math']:
 key=repo.replace('/','-');p=D/'sources'/(key+'-head.json');o=json.loads(p.read_text());report['registries'][repo]={'head':o['sha'],'head_receipt_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'commit_date':o['commit']['committer']['date'],'head_route':'https://api.github.com/repos/'+repo+'/commits/HEAD'}
for rec in json.loads((D/'outputs/fetch-search.json').read_text()):
 f=D/'sources'/rec['file'];o=json.loads(f.read_text());report['github_search'].append({**rec,'query':urllib.parse.parse_qs(urllib.parse.urlparse(rec['url']).query)['q'][0],'total_count':o.get('total_count'),'hits':[{'repo':x['full_name'],'description':(x.get('description') or '')[:300]} for x in o.get('items',[])]})
assert len(report['github_search'])==8
poolfiles=list((D/'sources').glob('pool-*'))
for i,row in rows.items():
 a=row['source_url'].split('/')[-1];s=(D/'sources'/('abs-'+a+'.html')).read_text();authors=re.findall(r'<meta name="citation_author" content="([^"]+)"',s);terms=[i,a]+[w.split(',')[0].split()[-1] for w in authors if w.split()];hits=[]
 for f in poolfiles:
  for ln,line in enumerate(f.read_text().splitlines(),1):
   matched=[x for x in terms if re.search(r'(?<![\w.])'+re.escape(x)+r'(?![\w.])',line,re.I)]
   if matched:hits.append({'file':str(f.relative_to(D)),'line':ln,'terms':matched,'text':line[:350]})
 report['targets'][i]={'source_arxiv':a,'authors':authors,'screen_terms':terms,'pool_hits':hits,'pool_scope':'LeanPool/projects.yml plus every blob in candidates/ at pinned HEAD; all bytes retained','outcome':'No matching prior target proof identified in pool metadata. Unrelated author/keyword matches are not exclusions.'}
report['actual_body_matches']={'375830':{'verdict':'excluded_prior_public_lean','files':['sources/omega-D5-S3-Combinatorics-Geometry-MiuraResolution.lean','sources/omega-Problems-gupta-2026-miura-residual-degree-conjecture-83.md'],'endpoint':'MiuraResolution.result : MiuraResidualCount.claim','scope':'All positive splits a+b=d>=5, one polynomial before dimensions, total degree<=d-3, original high region.'},'367197':{'verdict':'related_public_lemma_only; no full refutation claimed','file':'sources/omega-D5-S3-ConceptDynamics-GraphColoring-GraphCoverDomination.lean','endpoint':'regular_cover_small_domination','scope':'Every finite regular base has a (d+1)-fold cover with domination<=base order; unbounded regular domination ratio input not supplied by this file.'}}
(D/'outputs/registry-screen.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print({k:v['head'] for k,v in report['registries'].items()});print('queries',len(report['github_search']),'targets',len(report['targets']))
