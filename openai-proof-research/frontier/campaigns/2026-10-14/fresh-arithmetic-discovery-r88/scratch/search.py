from pathlib import Path
import re,json,hashlib,os
root=Path(__file__).resolve().parents[1];repo=root.parents[3]
queries={'algebra':r'Foulkes|Howe map|Donovan|Lipman.Zariski|stable.coordinate|Pixton|high.arity|klt.complement|Cartier.section|anticanonical.*(index|invariant)|nil algebra|Steinberg.*12', 'operations':r'Chow.variet|Chow variety|plethys|seminormal|divided.power|Gorenstein.index|ramification.*Morita|Cartier.*threshold'}
exclude={'private','inputs','input','dependencies','dependency','snapshots','snapshot','controls','control-copies','.git','node_modules','.lake','__pycache__','vendor','upstream','primary','sources'}
files=[]
for anchor in ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','experiments','proposals','scouts']:
 base=repo/anchor
 if not base.exists():continue
 for dirpath,dirs,names in os.walk(base):
  dirs[:]=[d for d in dirs if d not in exclude and not (Path(dirpath)/d).is_relative_to(root)]
  for n in names:
   p=Path(dirpath)/n
   if p.suffix.lower() in {'.md','.tex','.txt','.json','.py'} and not p.is_symlink(): files.append(p)
files=sorted(set(files));hits={k:[] for k in queries}; total=0
for p in files:
 data=p.read_bytes();total+=len(data);s=data.decode(errors='replace')
 for k,q in queries.items():
  for i,line in enumerate(s.splitlines(),1):
   if re.search(q,line,re.I):hits[k].append({'path':str(p.relative_to(repo)),'line':i,'text':line})
for k,h in hits.items():(root/f'packet/private/search/{k}.json').write_text(json.dumps(h,ensure_ascii=False,indent=2)+'\n')
(root/'packet/private/search/scope.json').write_text(json.dumps({'queries':queries,'files':len(files),'bytes':total,'max_size':max(p.stat().st_size for p in files),'excluded_components':sorted(exclude),'hidden_ignored_included':True,'size_cutoff':None,'hits':{k:len(v) for k,v in hits.items()}},indent=2)+'\n')
print('SCAN',len(files),total,'HITS',{k:len(v) for k,v in hits.items()})
seen=set()
for h in hits['algebra']:
 p=h['path']
 if 'fresh-arithmetic' in p and p not in seen and p.endswith('.md'):
  seen.add(p);print(p,':',h['text'][:180])
