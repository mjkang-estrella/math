import pathlib,json,re,subprocess,resource,hashlib
resource.setrlimit(resource.RLIMIT_AS,(1500*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(90,90))
L=pathlib.Path(__file__).resolve().parent.parent;D=json.loads((L/'extracted.json').read_text());ids=list(D);pat='|'.join(map(re.escape,ids+[x['record']['title'] for x in D.values()]))
p=subprocess.run(['rg','-l','-i',pat,'openai-proof-research','-g','*.md','-g','results.json','-g','ledger.json','-g','prior-campaign-context.json','-g','!**/corpus/**','-g','!**/raw/**','-g','!**/frozen/**','-g','!**/inputs/**','-g','!**/expanded-corpus-r36/**'],capture_output=True,text=True,timeout=75)
out={i:[] for i in ids}
for f in p.stdout.splitlines():
 s=pathlib.Path(f).read_text(errors='replace')
 for i,x in D.items():
  hits=[m for term in (i,x['record']['title']) if (m:=re.search(re.escape(term),s,re.I))]
  if hits:out[i].append({'path':f,'sha256':hashlib.sha256(pathlib.Path(f).read_bytes()).hexdigest(),'context':s[max(0,hits[0].start()-100):hits[0].end()+220]})
(L/'history-id-title-matches.json').write_text(json.dumps(out,indent=2)+'\n');print({i:len(v) for i,v in out.items()});print('rg exit',p.returncode)
