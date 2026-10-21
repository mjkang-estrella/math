import os, fnmatch, re, json, hashlib, sys
from pathlib import Path
P=Path.cwd(); R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r151'
assert P==Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
rounds={'arithmetic':[115,116,114,113,112,111,110,109,108,107], 'analytic':[145,146,144,143,142,141,140,139,138,137,136,135], 'structural':[151,150,149,148,147,146,145,144,143]}
globs=[f'*{k}*r{n}*' for k,ns in rounds.items() for n in ns]+['*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
tokens='corpus source primary history search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature .venv venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence seal'.split()
pat=re.compile(r'matroid.{0,60}prophet|prophet.{0,60}matroid|almighty|single.sample.{0,40}matroid|one.sample.{0,40}matroid',re.I)
if len(sys.argv)>1:pat=re.compile(sys.argv[1],re.I)
counts={'utf8':0,'nonutf8':0,'nul':0,'symlink':0,'pruned':0}; hits=[]; omitted=[]
def blocked(name):
 s=name.lower();return any(fnmatch.fnmatchcase(s,g) for g in globs) or any(t in s for t in tokens) or s=='.git'
for base,dirs,files in os.walk(P,topdown=True,followlinks=False):
 keep=[]
 for d in sorted(dirs):
  q=Path(base)/d
  if blocked(d) or q.is_symlink() or q==R: counts['pruned']+=1;omitted.append(str(q.relative_to(P)))
  else:keep.append(d)
 dirs[:]=keep
 for f in sorted(files):
  q=Path(base)/f; rel=str(q.relative_to(P))
  if blocked(f):counts['pruned']+=1;omitted.append(rel);continue
  if q.is_symlink():counts['symlink']+=1;continue
  try:b=q.read_bytes();s=b.decode('utf8')
  except UnicodeError:counts['nonutf8']+=1;continue
  if '\0' in s:counts['nul']+=1;continue
  counts['utf8']+=1
  if len(sys.argv)>1 and not re.search(r'matroid|prophet',s,re.I):continue
  lines=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if pat.search(l)]
  if lines:hits.append({'path':rel,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matches':lines})
out={'policy':{'globs':globs,'tokens':tokens,'no_size_cutoff':True,'hidden_ignored_json':True},'counts':counts,'hits':hits,'omitted_components':omitted}
(R/('private/history-mechanism.json' if len(sys.argv)>1 else 'private/history-scan.json')).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'counts':counts,'hit_files':len(hits),'hits':[{'path':h['path'],'lines':[l['line'] for l in h['matches']]} for h in hits]},indent=2))
