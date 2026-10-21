from pathlib import Path
import os,fnmatch,json,re,hashlib,sys
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r154')
patterns=json.loads((R/'original/exclusions.json').read_text())+['*.git*','*ten-findings*','*new-ten*','*status*','*progress*','*summary*','*summaries*']
output=sys.argv[1] if len(sys.argv)>1 else 'history-scan.json'
query=sys.argv[2] if len(sys.argv)>2 else r'polymatroid|common[ -](?:integer[ -])?bases|matroid[ -]intersection|weighted[ -]matroid'
if len(sys.argv)>2: patterns += ['*history*']
rx=re.compile(query,re.I)
rec={'patterns':patterns,'regex':rx.pattern,'path_basis':'full project-relative path, case insensitive','read':0,'non_utf8':0,'nul':0,'pruned':[],'hits':[],'errors':[]}
def banned(p): return any(fnmatch.fnmatchcase(p.lower(),x) for x in patterns)
for root,dirs,files in os.walk('.',topdown=True,followlinks=False):
 dirs.sort(); files.sort(); kept=[]
 for d in dirs:
  p=(Path(root)/d); s=p.as_posix()
  if p.is_symlink() or banned(s): rec['pruned'].append(s)
  else: kept.append(d)
 dirs[:]=kept
 for f in files:
  p=Path(root)/f; s=p.as_posix()
  if p.is_symlink() or banned(s): rec['pruned'].append(s); continue
  try: b=p.read_bytes()
  except OSError as e: rec['errors'].append([s,str(e)]); continue
  try: text=b.decode('utf-8')
  except UnicodeDecodeError: rec['non_utf8']+=1; continue
  if '\0' in text: rec['nul']+=1; continue
  rec['read']+=1
  hits=[{'line':i,'text':line} for i,line in enumerate(text.splitlines(),1) if rx.search(line)]
  if hits: rec['hits'].append({'path':s,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'matches':hits})
(R/'private'/output).write_text(json.dumps(rec,indent=2)+'\n')
print({k:rec[k] for k in ['read','non_utf8','nul','errors']});print('pruned',len(rec['pruned']),'hit files',len(rec['hits']))
for h in rec['hits']: print(h['path'], len(h['matches']))
