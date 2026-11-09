from pathlib import Path
import os,json,fnmatch,re,hashlib
r=Path(__file__).parent;g=json.loads((r/'guards.json').read_text())
def denied(p):
 s=p.as_posix().casefold()
 return s==g['ownRoot'].casefold() or s.startswith(g['ownRoot'].casefold()+'/') or any(x in s for x in g['substrings']) or any(fnmatch.fnmatchcase(s,w) for w in g['wildcards']+g['derivativePatterns'])
terms=[r'bounded[- ]scalar.{0,45}ricci[- ]flow',r'ricci[- ]flow.{0,45}(?:bounded[- ]scalar|smooth extension|curvature blow.?up)',r'ricci[- ]flat.{0,35}(?:tree inequality|degenerating tree|joined ends)',r'renormalized einstein.{0,4}hilbert',r'multivariable asymptotic path selection',r'joining[- ]length.{0,30}ricci error',r'capped ricci[- ]flow barriers',r'doubly[- ]warped.{0,60}(?:ricci|stolarski)',r'stolarski',r'critical spherical channel',r'collar[- ]dependent exterior',r'scalar[- ]curvature[- ]minus[- ]flux']
rx=re.compile('|'.join(terms),re.I)
heads=re.compile(r'^(#{1,6})\s+(.+)$|^\\((?:sub)*section)\*?\{([^}]+)\}',re.M)
admin=re.compile(r'status|provenance|scope.{0,12}evidence|contribution.{0,12}screen|acceptance|disposition|handoff|inventory|reading|audit|manifest|source list',re.I)
found=[];count=0;badutf=0;pruned=0
roots=['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','campaigns','iterations','experiments','proposals','scouts','notes','findings']
def walk(p):
 global pruned
 if denied(p):pruned+=1;return
 try:ents=os.scandir(p)
 except FileNotFoundError:return
 with ents:
  for ent in ents:
   q=Path(ent.path)
   if denied(q):pruned+=1;continue
   if ent.is_symlink():continue
   if ent.is_dir(follow_symlinks=False):yield from walk(q)
   elif ent.is_file(follow_symlinks=False):yield q
for scope in roots:
 for p in walk(Path(scope)):
  count+=1;b=p.read_bytes()
  try:s=b.decode('utf-8')
  except UnicodeDecodeError:badutf+=1;continue
  ms=list(rx.finditer(s))
  if not ms:continue
  hs=list(heads.finditer(s))
  selected=[]
  for m in ms:
   h=next((h for h in reversed(hs) if h.start()<=m.start()),None)
   title=h.group(2) or h.group(4) if h else '[no classified heading]'
   item={'match':m.group(),'char':m.start(),'heading':title,'heading_char':h.start() if h else None,'administrative':bool(admin.search(title)) or h is None}
   selected.append(item)
  found.append({'path':p.as_posix(),'sha256':hashlib.sha256(b).hexdigest(),'matches':selected})
(r/'history-navigation.json').write_text(json.dumps({'eligible_files_read_for_navigation':count,'non_utf8':badutf,'pruned_entries':pruned,'queries':terms,'hits':found,'limits':'Path heuristics are coarse; opaque false admissions possible. No body displayed by navigation; no exhaustive clearance.'},indent=2))
print(json.dumps({'files':count,'non_utf8':badutf,'pruned':pruned,'hits':found},indent=2))
