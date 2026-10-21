from pathlib import Path
import os,fnmatch,json,re
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
R=P/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r143'
rounds={'structural':[148,149,147,146,145,144,143], 'arithmetic':[113,114,112,111,110,109,108,107], 'analytic':[143,142,141,140,139,138,137,136,135]}
patterns=[f'*{a}*r{n}*' for a,ns in rounds.items() for n in ns]
patterns += ['*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
roles=['corpus','source','primary','history-derivative','search','inventory','fixture','control','extract','render','vendor','build','copy','copied','frozen','role','formal','manuscript','release','parent','private','input','upstream','shortlist','review','proof-gate','contribution','publication','packet','archive','cache','download','node_modules','.git','__pycache__']
patterns += [f'*{x}*' for x in roles]
def excluded(n): return any(fnmatch.fnmatchcase(n.lower(),pat) for pat in patterns)
rx=re.compile(r'infinity.harmonic|infinite.laplacian|infinity.laplacian|Source0?377|I377|gradient.{0,15}(flow|trajector|stream)|ascending.{0,12}(flow|stream)|Aronsson|Crandall.{0,12}Evans',re.I)
hits=[];counts={'utf8':0,'binary':0,'errors':0,'symlinks':0,'pruned':0};pruned=[]
for base,dirs,files in os.walk(P,topdown=True,followlinks=False):
 kept=[]
 for n in dirs:
  q=Path(base)/n
  if excluded(n) or q.is_symlink():
   counts['pruned']+=1;pruned.append(str(q.relative_to(P)))
  else: kept.append(n)
 dirs[:]=kept
 for n in files:
  if excluded(n): counts['pruned']+=1;continue
  q=Path(base)/n
  if q.is_symlink(): counts['symlinks']+=1;continue
  try:
   b=q.read_bytes()
   if b'\0' in b: counts['binary']+=1;continue
   s=b.decode('utf8');counts['utf8']+=1
  except UnicodeError: counts['binary']+=1;continue
  except OSError: counts['errors']+=1;continue
  found=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if rx.search(l)]
  if found:hits.append({'path':str(q.relative_to(P)),'hits':found})
(R/'private/history-scan.json').write_text(json.dumps({'patterns':patterns,'counts':counts,'hits':hits,'prunedDirectories':pruned},indent=2))
print(json.dumps(counts));print('matching files',len(hits))
for h in hits:
 print(h['path'])
 for x in h['hits'][:6]: print(str(x['line'])+': '+x['text'][:500])
