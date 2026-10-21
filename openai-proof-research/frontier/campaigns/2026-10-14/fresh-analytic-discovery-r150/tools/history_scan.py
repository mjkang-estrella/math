from pathlib import Path
import os,fnmatch,json,re
ROOT=Path.cwd(); out=ROOT/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r150'
p=json.loads((out/'private/ISOLATION-POLICY.json').read_text()); patterns=p['protected_fullpath_patterns']+p['broad_category_patterns']+['*history*','*screening*','*reading-*','*operation*','*summary*','*_proof*','*proof-r*']
query=re.compile(r'weighted.{0,50}(?:log.?BM|Brunn)|(?:log.?BM|Brunn).{0,60}(?:densit|measure)|density.flat|B.theorem|Saroglou',re.I)
stats={'decoded':0,'binary':0,'non_utf8':0,'pruned':0,'symlink':0,'errors':[]}; hits=[]
def banned(rel): return rel==p['own_root'] or rel.startswith(p['own_root']+'/') or any(fnmatch.fnmatchcase(rel.lower(),x) for x in patterns)
def walk(d):
 try: entries=sorted(os.scandir(d),key=lambda x:x.name)
 except OSError as e: stats['errors'].append(str(e)); return
 for ent in entries:
  rel=Path(ent.path).relative_to(ROOT).as_posix()
  if banned(rel): stats['pruned']+=1; continue
  if ent.is_symlink(): stats['symlink']+=1; continue
  if ent.is_dir(follow_symlinks=False): walk(ent.path)
  elif ent.is_file(follow_symlinks=False):
   try:
    raw=Path(ent.path).read_bytes()
    if b'\0' in raw: stats['binary']+=1; continue
    try: txt=raw.decode('utf8')
    except UnicodeDecodeError: stats['non_utf8']+=1; continue
    stats['decoded']+=1
    matches=[{'line':i,'text':l} for i,l in enumerate(txt.splitlines(),1) if query.search(l)]
    if matches: hits.append({'path':rel,'bytes':len(raw),'matches':matches})
   except OSError as e: stats['errors'].append(str(e))
for part in ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','iterations','experiments','proposals','scouts','notes','findings']:
 if (ROOT/part).is_dir(): walk(ROOT/part)
 else: stats.setdefault('absent_roots',[]).append(part)
(out/'private/history-weighted-hits.json').write_text(json.dumps({'query':query.pattern,'stats':stats,'hits':hits},indent=2)+'\n')
print(json.dumps(stats)); print('MATCHED_FILES',len(hits))
for h in hits: print(h['path'],h['bytes'],len(h['matches']))
