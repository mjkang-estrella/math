from pathlib import Path
import json,hashlib,fnmatch,os,re,urllib.request,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r155')
P=json.loads((R/'original/exclusions.json').read_text());guards=P['round_predicates']+P['coarse_predicates']
def excluded(s):return any(fnmatch.fnmatchcase(s.lower(),g) for g in guards)
query=re.compile(r'local[ -]flip|multicolou?r|multi.colou?r|hwang|knuth|kromatic|clone.{0,20}chromatic',re.I)
hits=[]; pruned=[];counts={'utf8':0,'nonutf8':0,'nul':0,'errors':0}
for root,dirs,files in os.walk('frontier',topdown=True,followlinks=False):
 parent=Path(root)
 ds=[]
 for n in dirs:
  q=parent/n;s=q.as_posix()
  if q.is_symlink() or excluded(s):pruned.append(s)
  else:ds.append(n)
 dirs[:]=ds
 for n in files:
  q=parent/n;s=q.as_posix()
  if q.is_symlink() or excluded(s):pruned.append(s);continue
  try:b=q.read_bytes();s0=b.decode('utf8')
  except UnicodeError:counts['nonutf8']+=1;continue
  except OSError:counts['errors']+=1;continue
  counts['utf8']+=1
  if '\0' in s0:counts['nul']+=1;continue
  found=[{'line':i,'text':l} for i,l in enumerate(s0.splitlines(),1) if query.search(l)]
  if found:hits.append({'path':s,'sha256':hashlib.sha256(b).hexdigest(),'matches':found})
(R/'private/history-primitives.json').write_text(json.dumps({'query':query.pattern,'counts':counts,'pruned':pruned,'hits':hits},indent=2)+'\n')
print('HISTORY COUNTS',counts,'pruned',len(pruned),'hit files',len(hits))
for h in hits:
 print(h['path'],[(x['line'],x['text'][:220]) for x in h['matches'][:5]])
