import os,re,json,fnmatch,hashlib
from pathlib import Path
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r163')
p=json.loads((R/'private/isolation-policy.json').read_text())
# Coarse extra exclusions deliberately sacrifice coverage; no trailing boundary.
coarse=p['coarse_component_prefix_categories']+['history','review','reading','seal','metadata','admin','generator']
def banned(path):
 s=str(path).lower()
 if s==str(R).lower() or s.startswith(str(R).lower()+'/'):return True
 if any(fnmatch.fnmatchcase(s,g) for g in p['full_path_case_insensitive_globs']):return True
 parts=re.split(r'[/_.\-\s]+',s)
 return any(x.startswith(c) for x in parts for c in coarse) or any(c in s for c in ['.git','direct.tex','summary.json','record_evidence','site-packages','third-party','new-ten','ten-findings','twenty-findings','second-history-screen','history-screen','history-broad-geometry','prepare.py','terminal-summary','checkpoint-output'])
rx=re.compile(r'trace[\s_-]*reconstruct|latest[\s_-]*anchor|spectrally[\s_-]*compact|deletion[\s_-]*(?:channel|trace)|burudgunte|quasipolynomial.{0,40}reconstruct|population.{0,30}reconstruct',re.I)
counts={'decoded_utf8':0,'non_utf8':0,'pruned':0,'symlinks':0,'errors':[]}; hits=[]
for top in ['frontier','campaigns','iterations','experiments','proposals','scouts','notes','findings']:
 if not Path(top).is_dir():continue
 for base,dirs,files in os.walk(top,topdown=True,followlinks=False):
  kept=[]
  for n in dirs:
   x=Path(base)/n
   if x.is_symlink():counts['symlinks']+=1;continue
   if banned(x):counts['pruned']+=1;continue
   kept.append(n)
  dirs[:]=kept
  for n in files:
   x=Path(base)/n
   if banned(x):counts['pruned']+=1;continue
   if x.is_symlink():counts['symlinks']+=1;continue
   try:b=x.read_bytes();s=b.decode('utf-8')
   except UnicodeDecodeError:counts['non_utf8']+=1;continue
   except OSError as e:counts['errors'].append([str(x),str(e)]);continue
   counts['decoded_utf8']+=1
   matches=[{'line':i,'text':line} for i,line in enumerate(s.splitlines(),1) if rx.search(line)]
   if matches:hits.append({'path':str(x),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matches':matches})
out={'counts':counts,'extra_coarse_guards':coarse,'hits':hits,'limits':'Prospective directory and file pruning; hidden/ignored/JSON/large eligible UTF8 have no size cutoff. Programs decode nonmatching eligible bodies, but semantic reading is only displayed matches and direct followups. Coarse omissions and opaque aliases preclude exhaustive or perfect-isolation claims.'}
(R/'private/history-screen-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(counts));print('Hit files',len(hits))
for h in hits:
 print(h['path'])
 for m in h['matches']: print(str(m['line'])+': '+m['text'])
