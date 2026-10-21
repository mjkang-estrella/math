"""Bounded-family history screening; prospective pruning, no size cutoff."""
from pathlib import Path
import os, fnmatch, json, re, hashlib
ROOT=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r162')
p=json.loads((ROOT/'private/isolation-policy.json').read_text())
# Additional conservative derivative/admin exclusions are prospective, not retroactive.
extra=['*history*','*seal*','*write_notes*','*review*','*reading*','*publication*','*diagnostic*','*acquisition*','*summary*','*summaries*','*screen*','*handover*','*metadata*','*adoption*','*intake*','*generated*','*generator*','*readme*','*rights*','*admin*']
p['additional_coarse_exclusions']=extra
(ROOT/'private/history-policy-01.json').write_text(json.dumps(p,indent=2)+'\n')
patterns=p['active_fullpath_case_insensitive']+p['broad_recent']+p['broad_aliases']+extra
query=re.compile(r'\bsandpile\b|\bchip[\s-]*firing\b|\bcritical[\s-]*group\b|\bparking[\s-]*function\b|\btoric\b|\bbinomial[\s-]*ideal\b|\bmarkov[\s-]*bas(?:is|es)\b',re.I)
receipt={'query':query.pattern,'policy':'history-policy-01.json','decoded':[],'pruned':[],'non_utf8':[],'errors':[],'hits':[],'symlinks':[]}
def exclude(path):
 s=path.as_posix().lower()
 return s==p['explicit_filename'].lower() or s==p['own_root'].lower() or any(fnmatch.fnmatchcase(s,x) for x in patterns) or path.name.lower() in p['directory_names']
starts=['frontier','campaigns','iterations','experiments','proposals','scouts','notes','findings']
for start in starts:
 if not Path(start).is_dir():continue
 for parent,dirs,files in os.walk(start,topdown=True,followlinks=False):
  kept=[]
  for d in sorted(dirs):
   path=Path(parent)/d
   if exclude(path):receipt['pruned'].append(str(path));continue
   if path.is_symlink():receipt['symlinks'].append(str(path));continue
   kept.append(d)
  dirs[:]=kept
  for name in sorted(files):
   path=Path(parent)/name
   if exclude(path):receipt['pruned'].append(str(path));continue
   if path.is_symlink():receipt['symlinks'].append(str(path));continue
   try:
    raw=path.read_bytes(); body=raw.decode('utf-8')
   except UnicodeDecodeError:receipt['non_utf8'].append(str(path));continue
   except OSError as e:receipt['errors'].append([str(path),str(e)]);continue
   receipt['decoded'].append({'path':str(path),'size':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
   hits=[{'line':n,'text':line} for n,line in enumerate(body.splitlines(),1) if query.search(line)]
   if hits:receipt['hits'].append({'path':str(path),'matches':hits})
(ROOT/'private/history-screen-01.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:len(v) for k,v in receipt.items() if isinstance(v,list)}))
for hit in receipt['hits']:
 print(json.dumps(hit))
