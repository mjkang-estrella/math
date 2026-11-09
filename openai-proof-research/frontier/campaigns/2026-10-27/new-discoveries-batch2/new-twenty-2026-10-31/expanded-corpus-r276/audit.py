import pathlib,json,hashlib,re,subprocess,resource,datetime
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).resolve().parent;root=next(x for x in p.parents if x.name=='openai-proof-research');r=json.loads((p/'reservation.json').read_text())
pat=r'\b(?:'+'|'.join(str(i) for i in r['ids'])+r')\b|'+'|'.join(re.escape(x['source_url'].split('/')[-1]) for x in r['rows'])+r'|BNDPF|two.Kuratowski|Steiner subratio|valid multisets'
cmd=['rg','-l','-i',pat,str(root/'frontier'),'-g','*.md','-g','*.json','-g','*.txt','-g','!**/corpus/**','-g','!**/frozen/**','-g','!**/inputs/**','-g','!**/sources/**','-g','!**/raw/**','-g','!**/expanded-corpus-r276/**','-g','!**/reservation.json','-g','!**/routing*','-g','!**/coverage*']
q=subprocess.run(cmd,capture_output=True,text=True,timeout=110);paths=q.stdout.splitlines();matches=[]
for x in paths:
 f=pathlib.Path(x)
 for n,line in enumerate(f.read_text(errors='replace').splitlines(),1):
  if re.search(pat,line,re.I):matches.append({'file':x,'line':n,'excerpt':line[:1200],'excerpt_truncated':len(line)>1200})
(p/'historical-search.json').write_text(json.dumps({'command':cmd,'exit':q.returncode,'stderr':q.stderr,'paths':paths,'matches':matches,'limits':'Bounded selected file-type text search; exclusions documented. Routing/reservation matches are not prior review.'},indent=2))
print('history paths',len(paths),'matches',len(matches))
source_inv=[]
for f in sorted((p/'sources').iterdir()):
 if f.suffix not in ['.txt','.html','.pdf']:continue
 source_inv.append({'file':str(f.relative_to(p)),'bytes':f.stat().st_size,'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'downloaded_not_necessarily_read':True})
(p/'source-inventory.json').write_text(json.dumps(source_inv,indent=2))
registry=[]
pat2='|'.join(str(i) for i in r['ids'])+r'|uniquely.*saturat|BNDPF|Kuratowski|Szeged|sole eigenvalue|multi.cluster|Steiner subratio'
for name in ['registry-projects.html','registry-openai.html']:
 f=p/'sources'/name;s=f.read_text();ms=[{'line':n,'text':l[:1000]} for n,l in enumerate(s.splitlines(),1) if re.search(pat2,l,re.I)]
 registry.append({'file':str(f.relative_to(p)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'matches':ms,'currentOid':sorted(set(re.findall(r'"currentOid":"([a-f0-9]{40})"',s))),'limits':'Catalogue/root-page term screen only; no complete tree and no matched Lean theorem body audited. Served HEAD content is not a repository pin.'})
(p/'registry-screen.json').write_text(json.dumps(registry,indent=2));print('registry match counts',[(x['file'],len(x['matches'])) for x in registry])
