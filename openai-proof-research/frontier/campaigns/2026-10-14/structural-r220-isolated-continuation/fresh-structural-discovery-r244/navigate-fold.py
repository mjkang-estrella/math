from pathlib import Path
import os,json,fnmatch,re,hashlib
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r244')
g=json.loads((R/'guards.json').read_text()); pats=g['full_path_casefold_wildcards']; subs=g['full_path_casefold_substrings']+['original-preservation']
def denied(p):
 s=p.as_posix().casefold()
 return s==R.as_posix().casefold() or s.startswith(R.as_posix().casefold()+'/') or any(fnmatch.fnmatchcase(s,q) for q in pats) or any(q in s for q in subs) or any(fnmatch.fnmatchcase(c,q) for c in s.split('/') for q in g['additional_component_patterns'])
# Highly specific aliases, evaluated only on eligible file bytes; no generic disjunctions.
qs=[r'Neumann.{0,100}nondegenera.{0,50}normal',r'Neumann.{0,100}(?:quadratic|quartic).{0,40}fold',r'eigenmap.{0,80}(?:fold|H[oö]lder|square.root|flatten)',r'boundary.{0,50}eigenmap.{0,50}curvature',r'Jerison.{0,30}Nadirashvili.{0,60}6[.]6']
regex=[re.compile(q,re.I) for q in qs];hits=[];counts={'eligible_files':0,'utf8_files':0,'rejected_entries':0,'symlinks_skipped':0};errors=[]
# No ancestors, no symlink following; prune before descent and file-byte reads.
stack=[Path('.')]
while stack:
 d=stack.pop()
 with os.scandir(d) as entries:
  for e in entries:
   p=Path(e.path)
   if denied(p):counts['rejected_entries']+=1;continue
   if e.is_symlink():counts['symlinks_skipped']+=1;continue
   if e.is_dir(follow_symlinks=False):stack.append(p);continue
   if not e.is_file(follow_symlinks=False):continue
   if p.as_posix()=='AGENTS.md':continue
   counts['eligible_files']+=1
   try:b=p.read_bytes();s=b.decode('utf-8')
   except UnicodeDecodeError:continue
   except OSError as x:errors.append([str(p),str(x)]);continue
   counts['utf8_files']+=1
   # Navigation only: return matched aliases and containing headings, never body contexts.
   lines=b.splitlines(keepends=True);off=0;heads=[]
   for i,l in enumerate(lines,1):
    t=l.decode('utf-8');m=re.match(r'^(#{1,6})\s+(.+)|\\((?:sub)*section)\*?\{([^}]+)\}',t)
    if m:heads.append((off,i,t.strip()))
    off+=len(l)
   for qi,q in enumerate(regex):
    for m in q.finditer(s):
     start=len(s[:m.start()].encode('utf-8'));last=next((h for h in reversed(heads) if h[0]<=start),None)
     htext=last[2] if last else '(no classified heading)'
     admin=bool(re.search(r'status|provenance|scope.and.evidence|contribution|acceptance|screen|handoff|summary|report|disposition|coordination',htext,re.I))
     hits.append({'path':p.as_posix(),'query':qs[qi],'byte':start,'heading':htext,'heading_line':last[1] if last else None,'administrative':admin,'sha256':hashlib.sha256(b).hexdigest()})
(R/'private/fold-navigation.json').write_text(json.dumps({'counts':counts,'hits':hits,'errors':errors,'limits':'Full-project-relative casefold prospective pruning. No body displayed. Hidden/ignored/JSON/large UTF8 eligible without size cutoff. Coarse aliases may omit originals; opaque aliases may evade exclusion. No exhaustive clearance.'},indent=2)+'\n')
print(json.dumps({'counts':counts,'hits':hits,'errors':errors},indent=2))
