"""Bounded one-family authored-history navigation. No symlink following."""
from pathlib import Path
import os,fnmatch,re,json,hashlib
PROJECT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
ROOT=PROJECT/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r148'
ROUND=['*arithmetic*r112*','*analytic*r142*','*arithmetic*r113*','*analytic*r143*','*structural*r147*','*structural*r146*','*structural*r145*','*analytic*r141*','*analytic*r140*','*analytic*r139*','*arithmetic*r111*','*arithmetic*r110*','*arithmetic*r109*','*arithmetic*r108*','*arithmetic*r107*','*analytic*r138*','*structural*r144*','*structural*r143*','*analytic*r137*','*analytic*r136*','*analytic*r135*','h138-*','t185r144-*','t177c143-*','t373e135-*','k369r134-*','t088p133-*']
# Deliberately coarse: excludes genuine originals with these names as well.
ALIASES=['corpus','source','primary','history','search','inventory','fixture','control','extract','render','vendor','build','copy','copied','copies','frozen','role','formal','manuscript','release','parent','private','payload','input','work','cache','download','snapshot','prior','brief','intake','task','dispatch','prompt','response','transcript','node_modules','.git','.lake','__pycache__','verify','replay','validation','audit','seal','check','manifest','receipt','envelope','attachment','archive','package','bundle','output','dist','target','publication','context','fetch','scratch','preprint','catalog','families','family-','author-','proof-r','contribution','review']
def blocked(name):
 s=name.lower()
 return any(fnmatch.fnmatchcase(s,p) for p in ROUND) or any(a in s for a in ALIASES) or s=='fresh-structural-discovery-r148'
QUERY=re.compile(r'rank[- ]layer|collapsed[- ]map|activation.{0,40}corner|biregular.{0,40}pattern|pattern.{0,40}biregular|singular.{0,40}Sidorenko|Sidorenko.{0,40}singular',re.I)
stats={'utf8':0,'non_utf8':0,'nul':0,'symlink':0,'pruned_dirs':0,'pruned_files':0}; hits=[]; agents=[]
for base,dirs,files in os.walk(PROJECT,topdown=True,followlinks=False):
 good=[]
 for d in sorted(dirs):
  f=Path(base)/d
  if f.is_symlink(): stats['symlink']+=1
  elif blocked(d): stats['pruned_dirs']+=1
  else: good.append(d)
 dirs[:]=good
 for n in sorted(files):
  f=Path(base)/n
  if f.is_symlink(): stats['symlink']+=1; continue
  if blocked(n): stats['pruned_files']+=1; continue
  if n=='AGENTS.md': agents.append(str(f.relative_to(PROJECT)))
  try: b=f.read_bytes(); t=b.decode('utf-8')
  except UnicodeDecodeError: stats['non_utf8']+=1;continue
  if '\x00' in t: stats['nul']+=1;continue
  stats['utf8']+=1
  match=[{'line':i,'text':s} for i,s in enumerate(t.splitlines(),1) if QUERY.search(s)]
  if match: hits.append({'path':str(f.relative_to(PROJECT)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matches':match})
out={'root':str(PROJECT),'round_patterns':ROUND,'coarse_aliases':ALIASES,'query':QUERY.pattern,'stats':stats,'agents':agents,'hits':hits,'limits':'No size cutoff. Hidden/ignored/JSON admitted subject to same pre-descent policy. Coarse omissions and arbitrary renamed derivatives not certified. Search is not reading or clearance.'}
(ROOT/'private/history-search-mechanism.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'stats':stats,'agents':agents,'hits':[{'path':h['path'],'matches':len(h['matches'])} for h in hits]},indent=2))
