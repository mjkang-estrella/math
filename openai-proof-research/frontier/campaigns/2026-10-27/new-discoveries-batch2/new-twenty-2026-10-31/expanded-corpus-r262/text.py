import pathlib,json,re,subprocess,resource,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent;start=time.monotonic();out={};jobs=[]
for p in sorted((L/'http').glob('*.abs.html')):
 i=p.name.split('.')[0];s=p.read_text(); versions=sorted(set(re.findall(r'/abs/([^"<> ]+v\d+)',s)));dois=re.findall(r'name="citation_doi" content="([^"]+)',s)
 out[i]={'versions':versions,'doi':dois}
 for v in versions:jobs.append([i+'-'+v.split('v')[-1]+'.pdf','https://arxiv.org/pdf/'+v])
for p in sorted((L/'http').glob('*.pdf')):
 q=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True,text=True,timeout=15)
 print(p.name,q.returncode,q.stderr[:200])
(L/'version-inventory.json').write_text(json.dumps(out,indent=2)+'\n');(L/'version-jobs.json').write_text(json.dumps(jobs))
print('elapsed',time.monotonic()-start)
