from pathlib import Path
import os,re,json,fnmatch,hashlib
ROOT=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r158')
p=json.loads((ROOT/'tools/isolation-policy.json').read_text())
p['body_prunes'] += ['history','comparison','reading-limit','isolation','session','incident','sawin','tao-teravainen','venieri','bright-dhar','hera','oberlin','younsi','ahlfors','bers','fetch','prepare','diagnostic','validate','verify','seal','bibliograph','references','node_modules','__pycache__','.venv']
(ROOT/'tools/isolation-policy.json').write_text(json.dumps(p,indent=2)+'\n')
patterns=p['prospective_fullpath']+p['completed_broad_prunes']+p['named_prunes']+p['extra_patterns']
def forbidden(path):
 s=path.as_posix().lower()
 if any(fnmatch.fnmatchcase(s,g) for g in patterns):return True
 return any(any(x in part for x in p['body_prunes']) for part in Path(s).parts)
needle=re.compile(r'kakeya|nikodym|furstenberg|critical[ -]path|unbounded[ -]narrowness|retained[ -]edge|source0?74|I0?02\b|I124\b',re.I)
rec=[];hits=[];skips={'directories':0,'files':0,'nonutf8':0,'symlink':0}
for directory,dirs,files in os.walk('.',topdown=True,followlinks=False):
 d=Path(directory)
 keep=[]
 for name in dirs:
  q=d/name
  if q.is_symlink():skips['symlink']+=1
  elif forbidden(q):skips['directories']+=1
  else:keep.append(name)
 dirs[:]=keep
 for name in files:
  q=d/name
  if q.is_symlink():skips['symlink']+=1;continue
  if forbidden(q):skips['files']+=1;continue
  b=q.read_bytes()
  try:s=b.decode('utf8')
  except UnicodeDecodeError:skips['nonutf8']+=1;continue
  rec.append({'path':str(q),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
  matches=[{'line':i,'tokens':sorted(set(m.group(0) for m in needle.finditer(line)))} for i,line in enumerate(s.splitlines(),1) if needle.search(line)]
  if matches:hits.append({'path':str(q),'matches':matches})
(ROOT/'private/authored-search-corrected.json').write_text(json.dumps({'decoded':rec,'hits':hits,'skips':skips},indent=2)+'\n')
print('Decoded',len(rec),'UTF8 files; skips',skips,'; hit files',len(hits))
for h in hits:
 if any(any(t.lower() in ['kakeya','critical-path','unbounded-narrowness'] for t in m['tokens']) for m in h['matches']):print(h)
