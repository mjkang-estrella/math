# Read-only project history walker. Outputs only under this round; not an isolation certificate.
from pathlib import Path
import json,re,fnmatch,os
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r126')
p=json.loads((R/'isolation-policy.json').read_text())
def banned(path):
 s=str(path).lower()
 return s.startswith(str(R).lower()) or any(fnmatch.fnmatchcase(s,g) for g in p['active_full_path_globs']+p['historical_full_path_globs']) or any(g.lower() in s for g in p['coarse_prefix_substring_guards'])
q=re.compile(r'generically[ -]free|versal.{0,20}torsor|essential\s+dimension|equivariant.{0,12}compression|field[s]? of definition|Uchida|Kummer',re.I)
hits=[];stats={'admitted_utf8':0,'pruned':0,'errors':0,'max_bytes':0}
for base in ['frontier','campaigns','iterations','experiments','proposals','scouts','notes','findings']:
 if not Path(base).is_dir():continue
 for root,ds,fs in os.walk(base,topdown=True,followlinks=False):
  kept=[]
  for d in ds:
   z=Path(root)/d
   if z.is_symlink() or banned(z):stats['pruned']+=1
   else:kept.append(d)
  ds[:]=kept
  for name in fs:
   z=Path(root)/name
   if z.is_symlink() or banned(z):stats['pruned']+=1;continue
   try:b=z.read_bytes();s=b.decode('utf8')
   except (OSError,UnicodeError):stats['errors']+=1;continue
   stats['admitted_utf8']+=1;stats['max_bytes']=max(stats['max_bytes'],len(b))
   m=[{'line':i,'text':line} for i,line in enumerate(s.splitlines(),1) if q.search(line)]
   if m:hits.append({'path':str(z),'matches':m})
(R/'private/history-navigation2.json').write_text(json.dumps({'stats':stats,'hits':hits},indent=2))
print(stats,'matching files',len(hits))
for x in hits:print(x['path'],[m['line'] for m in x['matches']])
