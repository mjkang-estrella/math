import os,json,hashlib,datetime,subprocess,urllib.request,urllib.error,re,gzip
from pathlib import Path
P=Path(__file__).resolve().parent; C=P.parents[3]; B=P.parent.parent
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
sha=lambda b:hashlib.sha256(b).hexdigest()
(P/'sources').mkdir(exist_ok=True)
# File-name-first duplicate screens, all campaign dates and case-insensitive report names.
patterns=[r'2401[.]15462|Fradelizi.{0,40}Gavalakis|Rapaport|isotropic.{0,30}extension|00813-7',r'5011394|random triangles.{0,30}(cone|cylinder)',r'2512[.]19003|Karlin.{0,15}Rinott']
reports=subprocess.check_output(['rg','--files','-g','*SUMMARY*','-g','*summary*','-g','*FINDINGS*','-g','*findings*','-g','*discovery*','-g','*provenance*',str(C)],text=True).splitlines()
reports=[f for f in reports if re.search(r'findings|summary|discovery|provenance',Path(f).name,re.I) and str(P) not in f]
out=[]
for pat in patterns:
 hits=[]
 # use rg -l before any section reading
 for i in range(0,len(reports),1000):
  r=subprocess.run(['rg','-l','-i',pat,*reports[i:i+1000]],capture_output=True,text=True)
  hits.extend(r.stdout.splitlines())
 sections=[]
 for f in hits[:24]:
  lines=Path(f).read_text(errors='replace').splitlines()
  for j,l in enumerate(lines):
   if re.search(pat,l,re.I):sections.append({'file':f,'line':j+1,'section':'\n'.join(lines[max(0,j-2):j+3])[:2600]})
 out.append({'pattern':pat,'filenames':hits,'bounded_actual_sections':sections[:35]})
(P/'duplicate-screen.json').write_text(json.dumps({'utc':now(),'campaign_root':str(C),'report_files':len(reports),'screens':out},indent=2))
ctx={}
for name in ['ledger.json','prior-campaign-context.json','NEXT.md','AGENTS.md']:
 data=(B/name).read_bytes();ctx[name]={'sha256':sha(data),'bytes':len(data)}
 if name.endswith('.json'):
  obj=json.loads(data);ctx[name]['keys']=list(obj)
  ctx[name]['titles']=[x.get('title',x.get('id')) for x in obj.get('accepted',[])]
  if name=='ledger.json':ctx[name]['candidate_statuses']=[{k:x.get(k) for k in ['id','status','scope']} for x in obj.get('candidates',[])]
 else:ctx[name]['lines']=len(data.splitlines())
(P/'context.json').write_text(json.dumps(ctx,indent=2))
freeze=B/'lanes/root-edge-irregulator-final-freeze-r1'; rr={}
for repo in ['omega','openai']:
 data=gzip.decompress((freeze/(repo+'-tree.txt.gz')).read_bytes()); lines=data.decode().splitlines()
 pat=r'Fradelizi|Rapaport|DiscreteEntropy|LatticeCovering/LogConcavity|LogConcaveQuery|KLS/Convexity/LogConcavity|isotropic.*extension|LogConcav.*(Extens|Lattice)|Lattice.*LogConcav'
 rr[repo]={'sha256':sha(data),'entries':len(lines),'matches':[x for x in lines if re.search(pat,x,re.I)],'delta_sha256':sha((freeze/(repo+'-delta.txt')).read_bytes())}
rr['snapshot']=json.loads((freeze/'CURRENT-REGISTRIES.json').read_text())
(P/'registry-screen.json').write_text(json.dumps(rr,indent=2))
urls=[('fgr-journal','https://link.springer.com/article/10.1007/s00454-025-00813-7'),('fgr-html','https://arxiv.org/html/2401.15462'),('fgr-abs','https://arxiv.org/abs/2401.15462'),('fgr-companion','https://www.dpmms.cam.ac.uk/~lg560/EPIdISIT.pdf'),('triangles','https://math.stackexchange.com/questions/5011394/conjecture-about-random-triangles-inscribed-in-cones-and-cylinders'),('madiman','https://arxiv.org/html/2512.19003v2'),('omega-head','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('openai-head','https://api.github.com/repos/openai/math/commits/HEAD'),('openai-query','https://raw.githubusercontent.com/openai/math/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/ComparatorChallenges/LogConcaveQuery.lean'),('openai-lattice','https://raw.githubusercontent.com/openai/math/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/LatticeCovering/LogConcavity.lean')]
log=[]
for name,url in urls:
 row={'name':name,'url':url,'utc':now()}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-research/1.0'})
  with urllib.request.urlopen(req,timeout=12) as r:
   b=r.read(6*1024*1024);row.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'),bytes=len(b),sha256=sha(b));(P/'sources'/name).write_bytes(b)
 except Exception as e:row.update(error=str(e))
 log.append(row);(P/'http.json').write_text(json.dumps(log,indent=2))
 print(name,row.get('status',row.get('error')),flush=True)
print(json.dumps({'duplicate_reports':len(reports),'matches':[(r['pattern'],len(r['filenames'])) for r in out],'registry_matches':{k:len(rr[k]['matches']) for k in ['omega','openai']}}))
