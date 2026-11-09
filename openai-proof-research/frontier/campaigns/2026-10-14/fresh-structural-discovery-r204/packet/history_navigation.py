from pathlib import Path
import os,json,hashlib,importlib.util
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r204')
s=importlib.util.spec_from_file_location('r204_guards',R/'guards.py');g=importlib.util.module_from_spec(s);s.loader.exec_module(g);g.compare_literals()
# Precise compounds and operative source mechanisms; no asymptotic O(n) search.
terms=['nonexpansive fixed point','nonexpansive fixed-point','nonexpansive map','non-expansive map','nonexpansive selfmap','reflexive fixed-point property','reflexive fixed point property','invariant convex subset','minimal invariant set','asymptotic center','asymptotic centre','adaptive finite selection','finite simultaneous approximation','compact semigroup','weighted switching','ideal cutoff','ideal-cutoff','anchor-tail','goebel--karlovitz','goebel–karlovitz','bruck','asymptotically nonexpansive','pointwise weak convergence','compact prediction']
# Exact authorized authored categories; missing/pruned roots are recorded, not replaced by a broad root walk.
roots=['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings']
hits=[];stats={'eligible_files':0,'utf8_files':0,'non_utf8_files':0,'utf8_bytes':0,'pruned_dirs':0,'pruned_files':0,'symlinks_skipped':0,'missing_or_pruned_roots':[]}
for start in roots:
 if g.excluded(start) or not Path(start).is_dir():stats['missing_or_pruned_roots'].append(start);continue
 for d,dirs,files in os.walk(start,topdown=True,followlinks=False):
  keep=[]
  for name in dirs:
   p=Path(d)/name
   if g.excluded(p):stats['pruned_dirs']+=1
   elif p.is_symlink():stats['symlinks_skipped']+=1
   else:keep.append(name)
  dirs[:]=keep
  for name in files:
   p=Path(d)/name
   if g.excluded(p):stats['pruned_files']+=1;continue
   if p.is_symlink():stats['symlinks_skipped']+=1;continue
   stats['eligible_files']+=1
   b=p.read_bytes()
   try:t=b.decode('utf-8')
   except UnicodeDecodeError:stats['non_utf8_files']+=1;continue
   stats['utf8_files']+=1;stats['utf8_bytes']+=len(b)
   if '\0' in t:continue
   found=[]
   for i,line in enumerate(t.splitlines(),1):
    lo=line.casefold(); matches=[term for term in terms if term in lo]
    if matches:found.append({'line':i,'terms':matches})
   if found:hits.append({'path':p.as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matches':found})
out={'guards':g.compare_literals(),'roots':roots,'terms':terms,'stats':stats,'hits':hits,'semantic_read':False,'limitations':'Prompt-level coarse path exclusions; hidden/ignored/JSON/large UTF8 included without size cutoff after pruning. No perfect classification or exhaustive clearance. Sources/history/copies, helper aliases and peer namespaces pruned before descent/read. Symlinks skipped.'}
(R/'private/history-navigation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
