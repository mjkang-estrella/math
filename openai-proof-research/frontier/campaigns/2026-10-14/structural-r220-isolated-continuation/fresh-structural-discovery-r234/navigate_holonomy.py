from pathlib import Path
import os,fnmatch,json,re,hashlib
ROOT=Path.cwd();OWN=Path(__file__).parent;g=json.loads((OWN/'guards.json').read_bytes())
def denied(path):
 s=path.as_posix().casefold()
 return any(fnmatch.fnmatchcase(s,x) for x in g['wildcards']) or any(x in s for x in g['substrings']) or any(fnmatch.fnmatchcase(c,p) for c in s.split('/') for p in g['extra_component_patterns'])
queries=[r'Seifert.{0,80}(?:translation holonomy|boundary.{0,35}character)',r'Gulliver.{0,80}(?:Riccati|buffer|index form)',r'graph[ -]manifold.{0,80}(?:concave cometric|conjugate[ -]points)',r'(?:boundary|circle[ -]valued).{0,35}holonomy.{0,60}(?:graph|Seifert)',r'no[ -]conjugate[ -]points.{0,80}(?:positive[ -]curvature patch|gluing graph)']
rx=re.compile('|'.join(queries),re.I)
admin=re.compile(r'status|provenance|scope|evidence|contribution|screen|intake|catalog|bibliograph|references|candidate|acceptance|disposition|sources|navigation|comparison|selection|campaign|handoff|summary|review|reading|limitations|inventory',re.I)
counts={'dirs_descended':0,'pruned_paths':0,'eligible_files_read':0,'non_utf8':0,'symlinks_skipped':0};hits=[]
def walk(d):
 for ent in sorted(os.scandir(d),key=lambda e:e.name.casefold()):
  p=Path(ent.path);rel=p.relative_to(ROOT)
  if denied(rel):counts['pruned_paths']+=1;continue
  if ent.is_symlink():counts['symlinks_skipped']+=1;continue
  if ent.is_dir(follow_symlinks=False):
   counts['dirs_descended']+=1;walk(p)
  elif ent.is_file(follow_symlinks=False):
   # Only potentially authored project branches, including hidden/ignored and every extension/size.
   if not any(c.casefold() in {'campaigns','iterations','experiments','proposals','scouts','notes','findings'} for c in rel.parts):continue
   b=p.read_bytes()
   try:s=b.decode('utf8')
   except UnicodeDecodeError:counts['non_utf8']+=1;continue
   counts['eligible_files_read']+=1
   lines=b.splitlines(keepends=True);offset=0;heads=[]
   for i,l in enumerate(lines):
    ls=l.decode();m=re.match(r'^(#{1,6})\s+(.+)',ls)
    if m:heads.append((offset,len(m[1]),m[2].strip(),i))
    offset+=len(l)
   starts=[];o=0
   for l in lines:starts.append(o);o+=len(l)
   for m in rx.finditer(s):
    pos=len(s[:m.start()].encode('utf8'));hs=[h for h in heads if h[0]<=pos]
    if not hs:head=(0,0,'UNCLASSIFIED NO HEADING',0)
    else:head=hs[-1]
    end=next((h[0] for h in heads if h[0]>head[0] and h[1]<=head[1]),len(b))
    hrec={'path':rel.as_posix(),'heading':head[2],'start':head[0],'end':end,'match_byte':pos,'matched_query':next(q for q in queries if re.search(q,m.group(0),re.I)),'classification':'REJECT admin heading' if admin.search(head[2]) else 'NEEDS HEADING CLASSIFICATION','file_sha256':hashlib.sha256(b).hexdigest()}
    if not any(x['path']==hrec['path'] and x['start']==hrec['start'] for x in hits):hits.append(hrec)
walk(ROOT)
obj={'guards_sha256':hashlib.sha256((OWN/'guards.json').read_bytes()).hexdigest(),'queries':queries,'counts':counts,'hits':hits,'limits':'No exhaustive clearance. Pruned aliases and directories can omit useful originals; opaque derivatives can escape. No body displayed by this navigation.'}
(OWN/'private/history-navigation.json').write_text(json.dumps(obj,indent=2)+'\n');print(json.dumps(obj,indent=2))
