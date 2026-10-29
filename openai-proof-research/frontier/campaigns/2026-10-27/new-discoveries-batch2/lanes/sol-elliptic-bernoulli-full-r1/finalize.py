import pathlib,json,hashlib,datetime,re,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,30));signal.alarm(40)
b=pathlib.Path(__file__).parent;B=b.parent.parent;R=B.parents[3]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
inputs=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'NEXT.md',B/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md',B/'lanes/sol-fresh-source-discovery-r37/discovery.md',B/'lanes/sol-fresh-source-discovery-r37/provenance.json',B/'lanes/sol-fresh-source-discovery-r37/registry-screen.json',B/'lanes/root-fresh-source-r37-handback/ADOPTION.json']
records=[]
for p in inputs:
 s=p.read_text();records.append({'path':str(p.resolve()),'sha256':sha(p),'bytes_read':len(s.encode())})
old=json.loads((B/'lanes/sol-fresh-source-discovery-r37/registry-screen.json').read_text())
queries=['bernoulli','elliptic','grosset','faulhaber','weierstrass'];scopes=[]
for item in old['scopes']:
 p=R.parent/pathlib.Path(item['inherited'])
 d=json.loads(p.read_text())
 if isinstance(d,list):paths=[v if isinstance(v,str) else v.get('path','') for v in d]
 elif isinstance(d,dict):paths=[v.get('path','') if isinstance(v,dict) else v for v in d.get('tree',d.get('paths',[]))]
 hits=[v for v in paths if any(q in v.lower() for q in queries)]
 scopes.append({'scope':item['scope'],'path':str(p.resolve()),'sha256':sha(p),'entries':len(paths),'hits':hits,'scope_note':'Inherited scope only; see r37 delta chain. Not whole Omega dev.'})
heads={}
for name in ['omega','omega-main','openai','aim','count']:
 d=json.loads((b/'sources'/f'{name}-head.json').read_text());heads[name]=d['sha']
delta=json.loads((b/'sources/omega-delta.json').read_text())
reg={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'heads':heads,'scopes':scopes,'delta':{'base':old['heads']['omega'],'head':heads['omega'],'commits':delta['total_commits'],'files':[f['filename'] for f in delta['files']],'latest_utc':delta['commits'][-1]['commit']['committer']['date']},'limitations':['No whole Omega-dev coverage','Colbrook recursive tree truncated=true:43443 entries','No registry absence implies novelty','No worldwide prior-art clearance'],'novelty_pass':False,'disposition':'routine classical corollary; no novelty nomination'}
(b/'registry-screen.json').write_text(json.dumps(reg,indent=2)+'\n')
manifest=[{'file':str(p.relative_to(b)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted((b/'sources').iterdir()) if p.is_file()]
(b/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'credit':0,'counts':'5 additional /35 total unchanged','disposition':'routine classical corollary; mathematical investment stopped','inputs':records,'http_log':'http.json','primary_manifest':'manifest.json','registry':'registry-screen.json','checks':'checks.json','ordinary_proof':'PROOF.md','formal_status':'No Lean written or run; no complete formal endpoint claimed','holds':['2006 VoR PDF403: not obtained; no published-version comparison','Institutional handle202/0bytes: stopped','Handbook download hit fetch16MB ceiling; partial/unusable; NOT relied on','Citeseer heat PDF404; canonical arXiv primary obtained','Mistaken mcolbrook.github.io404; canonical DAMTP author page obtained'],'acceptance':'Root only; no nomination or count change'}
(b/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
print('heads',heads)
for s in scopes:print(s['scope'],s['entries'],len(s['hits']),s['hits'][:25])
