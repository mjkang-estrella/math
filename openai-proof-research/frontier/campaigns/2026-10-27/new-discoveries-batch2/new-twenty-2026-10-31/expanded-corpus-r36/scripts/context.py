import pathlib,json,hashlib,subprocess,resource
resource.setrlimit(resource.RLIMIT_AS,(1500*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(90,90))
B=pathlib.Path('openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2');L=B/'new-twenty-2026-10-31/expanded-corpus-r36';D=json.loads((L/'extracted.json').read_text());pat='|'.join(D)
p=subprocess.run(['rg','-l',pat,str(B),'-g','*.md','-g','results.json','-g','ledger.json','-g','prior-campaign-context.json','-g','!**/corpus/**','-g','!**/raw/**','-g','!**/frozen/**','-g','!**/inputs/**','-g','!**/expanded-corpus-r36/**'],capture_output=True,text=True,timeout=70)
files=p.stdout.splitlines();out={i:[] for i in D}
for f in files:
 try:
  s=pathlib.Path(f).read_text()
  for i in D:
   if i in s:out[i].append({'path':f,'sha256':hashlib.sha256(s.encode()).hexdigest(),'contexts':[s[max(0,m-160):m+500] for m in [s.find(i)]]})
 except Exception:pass
(L/'history-matches.json').write_text(json.dumps(out,indent=2)+'\n')
ctx=[]
for f in [B/'ledger.json',B/'prior-campaign-context.json',B/'new-twenty-2026-10-31/ledger.json']:
 d=json.loads(f.read_text());ctx.append({'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'keys':list(d),'dispositions':{k:v for k,v in d.items() if k not in ['lanes','followups','published_papers']}})
(L/'administrative-context.json').write_text(json.dumps(ctx,indent=2)+'\n')
print(json.dumps(out,indent=2))
