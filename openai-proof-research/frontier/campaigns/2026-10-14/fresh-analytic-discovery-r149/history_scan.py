from pathlib import Path
import os,json,fnmatch,re,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r149');policy=json.loads((R/'private/exclusions.json').read_text())
globs=policy['active_and_recent_literal_globs']+policy['broad_body_category_globs']+['*analytic*r149*','*proof-r*']
def excluded(p):return any(fnmatch.fnmatchcase(str(p).lower(),g) for g in globs)
roots=[Path(p) for p in ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','proposals','iterations','experiments','scouts','notes','findings']]
pat=re.compile(r'lieb[–− -]?thirring|one.bound.state|matrix.solito[n]|spectral.deficit|isospectral|sech\^?\{?2',re.I)
stats={'decoded':0,'binary':0,'nonutf8':0,'symlinks':0,'pruned':0,'errors':[],'missing_roots':[]}; hits=[]
for root in roots:
 if not root.exists():stats['missing_roots'].append(str(root));continue
 for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
  keep=[]
  for d in ds:
   p=Path(base)/d
   if excluded(p):stats['pruned']+=1
   elif p.is_symlink():stats['symlinks']+=1
   else:keep.append(d)
  ds[:]=keep
  for n in fs:
   p=Path(base)/n
   if excluded(p):stats['pruned']+=1;continue
   if p.is_symlink():stats['symlinks']+=1;continue
   try:b=p.read_bytes()
   except OSError as e:stats['errors'].append([str(p),str(e)]);continue
   if b'\0' in b:stats['binary']+=1;continue
   try:s=b.decode('utf8')
   except UnicodeDecodeError:stats['nonutf8']+=1;continue
   stats['decoded']+=1
   matches=[{'line':i+1,'text':l} for i,l in enumerate(s.splitlines()) if pat.search(l)]
   if matches:hits.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matches':matches})
(R/'private/history/scan-results.json').write_text(json.dumps({'stats':stats,'hits':hits},indent=2)+'\n')
print(json.dumps(stats));print('MATCHING_FILES',len(hits))
for h in hits:
 print(h['path'],len(h['matches']),'matching lines')
 for m in h['matches'][:2]:print(' ',m['line'],m['text'][:450])
