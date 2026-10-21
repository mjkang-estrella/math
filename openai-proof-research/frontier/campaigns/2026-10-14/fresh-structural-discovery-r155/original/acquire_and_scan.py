from pathlib import Path
import json,hashlib,fnmatch,os,re,urllib.request,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r155')
P=json.loads((R/'original/exclusions.json').read_text());guards=P['round_predicates']+P['coarse_predicates']
def excluded(s):return any(fnmatch.fnmatchcase(s.lower(),g) for g in guards)
query=re.compile(r'chromatic.{0,25}(?:quasi)?symmetric|shareshian|\bwachs\b|guay.paquet|hessenberg|stanley.stembridge|unit.interval.{0,30}positiv',re.I)
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
(R/'private/history-scan.json').write_text(json.dumps({'query':query.pattern,'counts':counts,'pruned':pruned,'hits':hits},indent=2)+'\n')
print('HISTORY COUNTS',counts,'pruned',len(pruned),'hit files',len(hits))
for h in hits:
 print(h['path'],[(x['line'],x['text'][:220]) for x in h['matches'][:5]])
entries=json.loads((R/'private/selected-source-navigation.json').read_text())
pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def fetch(e):
 url=f'https://raw.githubusercontent.com/openai/math/{pin}/'+e['path']
 b=urllib.request.urlopen(url,timeout=45).read()
 sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and sha==e['sha']
 dst=R/'private/source'/Path(e['path']).name;dst.write_bytes(b)
 return {'canonical_path':e['path'],'pinned_url':url,'size':len(b),'git_blob_sha1':sha,'sha256':hashlib.sha256(b).hexdigest(),'member':str(dst.relative_to(R))}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:ident=list(ex.map(fetch,[e for e in entries if e['type']=='blob' and not e['path'].endswith('.pdf')]))
(R/'private/source-identities.json').write_text(json.dumps(ident,indent=2)+'\n')
print('AUTHENTICATED',len(ident),'source files')
