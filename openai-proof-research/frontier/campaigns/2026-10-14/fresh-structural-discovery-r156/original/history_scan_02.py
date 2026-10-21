from pathlib import Path
import os,json,fnmatch,re,hashlib
root=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r156')
patterns=json.loads((root/'original/exclusions-amended.json').read_text())
def excluded(p):return any(fnmatch.fnmatchcase(p.lower(),q) for q in patterns)
rx=re.compile(r'Steinberg|Whitney homology|radical.{0,20}(subgroup|poset)|local homology|subgroup.{0,20}interval|Quillen.{0,15}(complex|homology|poset)' ,re.I)
record={'patterns':patterns,'pruned':[],'non_utf8':[],'symlinks':[],'decoded':0,'hits':[]}
for base,dirs,files in os.walk('.',topdown=True,followlinks=False):
 dirs.sort();files.sort()
 keep=[]
 for d in dirs:
  p=(Path(base)/d);s=p.as_posix().removeprefix('./')
  if p.is_symlink():record['symlinks'].append(s)
  elif excluded(s):record['pruned'].append(s+'/')
  else:keep.append(d)
 dirs[:]=keep
 for f in files:
  p=Path(base)/f;s=p.as_posix().removeprefix('./')
  if excluded(s):record['pruned'].append(s);continue
  if p.is_symlink():record['symlinks'].append(s);continue
  if not p.is_file():continue
  b=p.read_bytes()
  try:t=b.decode('utf8')
  except UnicodeDecodeError:record['non_utf8'].append(s);continue
  record['decoded']+=1
  hits=[{'line':i,'text':line} for i,line in enumerate(t.splitlines(),1) if rx.search(line)]
  if hits:record['hits'].append({'path':s,'sha256':hashlib.sha256(b).hexdigest(),'matches':hits})
(root/'private/history-scan-02.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:len(v) if isinstance(v,list) else v for k,v in record.items() if k!='patterns'}))
for h in record['hits']:
 print(h['path'])
 for m in h['matches'][:3]:print(m['line'],m['text'][:450])
