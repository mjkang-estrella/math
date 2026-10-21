from pathlib import Path
import os,fnmatch,json,re,time
ROOT=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r157')
p=json.loads((ROOT/'receipts/prospective-policy.json').read_text())
patterns=sum([v for k,v in p.items() if k.endswith('_globs')],[])
patterns += ['*dispatch*','*write_notes*','*review*']
pattern=re.compile(r'(?:source|family|screen)[ _-]*168|terminal.kernel|edge.image|Deodhar|Barkley|Braden|MacPherson|Lanini|biclosed|twisted.Verma',re.I)
start=time.monotonic();r={'patterns':patterns,'query':pattern.pattern,'read_utf8':0,'non_utf8':[],'pruned':[],'hits':[]}
def excluded(s):
 return next((x for x in patterns if fnmatch.fnmatchcase('/'+s.lower(),x)),None)
for base,ds,fs in os.walk('.',topdown=True,followlinks=False):
 if time.monotonic()-start>55: raise RuntimeError('bounded scan exceeded; no completed receipt')
 ds.sort();fs.sort()
 for d in ds[:]:
  q=Path(base)/d;s=q.as_posix();why=excluded(s)
  if why or q.is_symlink(): ds.remove(d);r['pruned'].append([s,why or 'symlink'])
 for f in fs:
  q=Path(base)/f;s=q.as_posix();why=excluded(s)
  if why or q.is_symlink():r['pruned'].append([s,why or 'symlink']);continue
  try:t=q.read_bytes().decode('utf8')
  except UnicodeDecodeError:r['non_utf8'].append(s);continue
  r['read_utf8']+=1
  hits=[{'line':i+1,'text':line} for i,line in enumerate(t.splitlines()) if pattern.search(line)]
  if hits:r['hits'].append({'path':s,'matches':hits})
r['elapsed']=time.monotonic()-start;r['complete']=True
(ROOT/'private/history-screen02.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'read_utf8':r['read_utf8'],'non_utf8':len(r['non_utf8']),'pruned':len(r['pruned']),'hit_files':len(r['hits']),'elapsed':r['elapsed']}))
for h in r['hits']:
 print(h['path'],len(h['matches']))
 for m in h['matches'][:4]: print(m['line'],m['text'][:700])
