import runpy
D=runpy.run_path(__file__.replace('registry.py','research.py'));globals().update({k:v for k,v in D.items() if not k.startswith('__')})
import urllib.request,re
h=[]
for repo in ['openai/math','Vilin97/lean-pool','TauCetiProject/TauCeti','leanprover-community/mathlib4']:
 url='https://github.com/'+repo;t=now()
 try:
  with urllib.request.urlopen(url,timeout=18) as r:b=r.read();status=r.status;final=r.url
  heads=list(dict.fromkeys(re.findall(r'"currentOid":"([0-9a-f]{40})"',b.decode())))
  name=repo.replace('/','-');write('registry/'+name+'.html',b.decode());h.append({'url':url,'utc':t,'status':status,'final_url':final,'bytes':len(b),'sha256':sha(b),'heads':heads,'depth':'root catalogue metadata only; no theorem-body clearance'})
  print(repo,heads)
 except Exception as e:h.append({'url':url,'utc':t,'error':str(e),'no_retry':True});print(repo,'ERROR',str(e))
for name in ['CONTENTS.md','preprints-tree.json']:
 p=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources')/name;b=read(p);lines=b.decode().splitlines();matches=[x for x in lines if any(w in x.lower() for w in ['zonotop','nenashev','necklace','kaon','coefficient-sum']) and not any(w in x.lower()for w in ['crown','bunkbed','tournament'])];print('PINNED CATALOGUE',name,matches)
write('registry-receipts.json',h);write('registry-resources.json',receipts)
print('TRUE_EXIT',0,'PID',os.getpid(),'RUSAGE',list(resource.getrusage(resource.RUSAGE_SELF)))
