import os,re,json,hashlib
from path_policy import ROOT,OWN,excluded
query=re.compile(r'Colin.de.Verdi|Hadwiger|connected.matching|correspondence.colou?r|DP.colou?r|well.signed|strong.Arnold|clique.blow.up|woven|list.colou?r|eligible.thinning',re.I)
counts={'utf8':0,'nonutf8':0,'pruned':0,'symlink':0};hits=[];admitted=[];pruned=[]
for d,dirs,files in os.walk(ROOT,topdown=True,followlinks=False):
 for n in list(dirs):
  p=ROOT/os.path.relpath(os.path.join(d,n),ROOT);why=excluded(p)
  if why or p.is_symlink():dirs.remove(n);counts['pruned']+=1;pruned.append([p.relative_to(ROOT).as_posix(),why or 'symlink'])
 for n in files:
  p=ROOT/os.path.relpath(os.path.join(d,n),ROOT);why=excluded(p)
  if why:counts['pruned']+=1;pruned.append([p.relative_to(ROOT).as_posix(),why]);continue
  if p.is_symlink():counts['symlink']+=1;continue
  try:b=p.read_bytes();s=b.decode('utf8')
  except (UnicodeError,OSError):counts['nonutf8']+=1;continue
  counts['utf8']+=1;rel=p.relative_to(ROOT).as_posix();admitted.append([rel,len(b),hashlib.sha256(b).hexdigest()])
  found=[{'line':i,'text':line} for i,line in enumerate(s.split('\n'),1) if query.search(line)]
  if found:hits.append({'path':rel,'sha256':hashlib.sha256(b).hexdigest(),'matches':found})
for name,obj in [('history-query.json',hits),('history-admitted.json',admitted),('history-pruned.json',pruned),('history-counts.json',counts)]:
 (OWN/'private'/name).write_text(json.dumps(obj,indent=2))
print(counts)
for h in hits:print(h['path'],[(m['line'],m['text'][:160]) for m in h['matches']][:12])
