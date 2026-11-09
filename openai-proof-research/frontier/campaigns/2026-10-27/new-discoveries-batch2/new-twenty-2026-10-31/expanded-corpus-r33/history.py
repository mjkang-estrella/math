import pathlib,json,subprocess,hashlib,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
o=pathlib.Path(__file__).resolve().parent;root=pathlib.Path('openai-proof-research');ds=json.loads((o/'literal-provenance.json').read_text());out={}
for i,v in ds.items():
 pats=[r'\b'+i+r'\b',v['record']['title']]
 matches=[]
 for pat in pats:
  r=subprocess.run(['rg','-l','-i',pat,str(root),'-g','*.md','-g','*results*.json','-g','*review*.json','-g','*ledger*.json','-g','!reservation.json','-g','!literal-provenance.json','-g','!registry*.json','-g','!coverage*.json','-g','!manifest*.json'],capture_output=True,text=True,timeout=30)
  for s in r.stdout.splitlines():
   if str(o.relative_to(pathlib.Path.cwd())) in s:continue
   p=pathlib.Path(s)
   if p.name=='ledger.json' and 'new-twenty' in s:continue
   if s not in [x['path'] for x in matches]:
    t=p.read_text(errors='replace'); import re
    m=re.search(pat,t,re.I);matches.append({'path':s,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'excerpt':t[max(0,m.start()-200):m.end()+450] if m else ''})
 out[i]=matches
(o/'history-matches.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');print({i:len(m) for i,m in out.items() if m})
