import pathlib,json,subprocess,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent; C=L.parent
r=json.loads((L/'literal-records.json').read_text()); jobs=[]
for a in sorted(set(x['record']['source_url'].split('/')[-1] for x in r.values())):
 jobs.extend([[a+'-abs','https://arxiv.org/abs/'+a],[a+'-pdf','https://arxiv.org/pdf/'+a]])
for n,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:jobs.append([n+'-head','https://api.github.com/repos/'+repo+'/commits/HEAD'])
(L/'jobs.json').write_text(json.dumps(jobs))
p=subprocess.run(['rg','-l','|'.join(r),str(C.parent),'-g','results.json','-g','SUMMARY.md','-g','*rejection*','-g','*REVIEW*.md'],capture_output=True,text=True)
hits={}
for path in p.stdout.splitlines():
 pth=pathlib.Path(path)
 if pth.parent==L:continue
 s=pth.read_text(errors='replace'); hits[path]=s
(L/'history-bodies.json').write_text(json.dumps(hits,indent=2))
print('\n'.join(hits))
