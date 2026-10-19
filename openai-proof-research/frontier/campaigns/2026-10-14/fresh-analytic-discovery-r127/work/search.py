from pathlib import Path
import subprocess,re,json,hashlib
root=Path(__file__).resolve().parents[1];repo=root.parents[3];out=root/'packet/private/search'
roots=[str(repo/x) for x in ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/scouts'] if (repo/x).exists()]
raw=subprocess.check_output(['rg','--files','--hidden','--no-ignore',*roots]);paths=raw.decode().splitlines()
exclude={'node_modules','.git','.lake','private','inputs','input','upstream','primary','context','vendor','vendored','site-packages','__pycache__','render','renders','snapshots','snapshot','provenance'}
pat=re.compile(r'bi.?Sobolev|inverse.{0,30}(gradient|Sobolev|approximat)|Ball.{0,5}Evans|nonexpansive|amenable semigroup|Lipschitz.free|elasticity|Lam[eé]|transport.matching',re.I)
hits=[];inv=[];errors=[]
for s in paths:
 p=Path(s)
 if root in p.parents or any(c in exclude for c in p.relative_to(repo).parts) or p.suffix.lower() not in {'.md','.txt','.json','.tex','.py','.lean','.yaml','.yml','.csv','.tsv','.log','.sh',''}:continue
 try:b=p.read_bytes();text=b.decode('utf8')
 except UnicodeDecodeError:continue
 except Exception as e:errors.append([str(p),str(e)]);continue
 inv.append([str(p.relative_to(repo)),len(b),hashlib.sha256(b).hexdigest()])
 for i,l in enumerate(text.splitlines(),1):
  if pat.search(l):hits.append({'path':str(p.relative_to(repo)),'line':i,'text':l})
(out/'hits.json').write_text(json.dumps(hits,ensure_ascii=False,indent=2));(out/'inventory.json').write_text(json.dumps(inv,indent=2));receipt={'roots':roots,'excluded_components':sorted(exclude),'pattern':pat.pattern,'no_size_cutoff':True,'files':len(inv),'bytes':sum(x[1] for x in inv),'largest':max(x[1] for x in inv),'hits':len(hits),'errors':errors};(out/'receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2));print('\n'.join(sorted(set(x['path'] for x in hits if '/campaigns/' in x['path'] and '/packet/public/' in x['path']))))
