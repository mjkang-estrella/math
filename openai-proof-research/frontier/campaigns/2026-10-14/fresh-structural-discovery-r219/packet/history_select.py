from pathlib import Path
import os,json,fnmatch,re,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r219/packet')
p=json.loads((R/'private/guards.json').read_text())
def blocked(rel):
 s=rel.casefold()
 return s==str(R).casefold() or s.startswith(str(R).casefold()+'/') or any(x in s for x in p['substrings']) or any(fnmatch.fnmatchcase(s,w) for w in p['wildcards']) or any(fnmatch.fnmatchcase(part,w) for part in s.split('/') for w in p['derivative_component_patterns'])
assert all(blocked('frontier/campaigns/X/'+w.strip('*').replace('*','_')+'/a.tex') for w in p['wildcards'])
queries=[r'higher[ -]dimensional symplectic ball pack',r'siegel[\s–—-]+yao',r'closed[ -]ball neighborhood pack',r'symplectic packing pairwise capacity',r'relative symplectic packing extension',r'hamiltonian comparison',r'moser with outer faces',r'packing over a (?:positive[ -]genus base|surface with a handle)',r'(?:countable|locally finite)[^\n]{0,60}symplectic[^\n]{0,30}pack',r'symplectic[^\n]{0,50}(?:countable|locally finite)',r'(?:symplectic|ball) packing[^\n]{0,80}(?:shell|normal[ -]cone|degeneration)',r'normal[ -]cone[^\n]{0,80}(?:symplectic|packing)']
rx=re.compile('|'.join(queries),re.I)
heading=re.compile(r'^(#{1,6})\s+(.+)|^\\(section|subsection|subsubsection|paragraph)\*?\{([^}]+)\}')
admin=re.compile(r'status|provenance|scope.and.evidence|contribution.screen|administrative|disposition|handoff|intake|receipt|gate|acceptance|review|audit|manifest|summary|coordination|task|campaign|catalog|source list|reference|bibliograph',re.I)
records=[]; stats={'eligible_utf8':0,'non_utf8':0,'pruned_entries':0,'symlinks_skipped':0,'matching_files':0,'rejected_administrative_matches':0,'unsectioned_matches':0}
roots=[Path(prefix+name) for prefix in ['frontier/',''] for name in ['campaigns','iterations','experiments','proposals','scouts','notes','findings']]
seen=set()
def walk(d):
 if blocked(d.as_posix()):return
 if not d.is_dir():return
 with os.scandir(d) as it:
  for e in it:
   rel=Path(e.path).as_posix()
   if blocked(rel):stats['pruned_entries']+=1;continue
   if e.is_symlink():stats['symlinks_skipped']+=1;continue
   if e.is_dir(follow_symlinks=False):yield from walk(Path(e.path))
   elif e.is_file(follow_symlinks=False):yield Path(e.path)
for d in roots:
 for f in walk(d):
  if f in seen:continue
  seen.add(f)
  b=f.read_bytes()
  try:s=b.decode('utf-8')
  except UnicodeDecodeError:stats['non_utf8']+=1;continue
  stats['eligible_utf8']+=1
  if not rx.search(s):continue
  stats['matching_files']+=1
  lines=b.splitlines(keepends=True);off=0;heads=[];matches=[]
  for n,l in enumerate(lines,1):
   v=l.decode();m=heading.match(v)
   if m:heads.append({'line':n,'byte':off,'level':len(m[1]) if m[1] else {'section':1,'subsection':2,'subsubsection':3,'paragraph':4}[m[3]],'title':m[2] or m[4]})
   if rx.search(v):matches.append(n)
   off+=len(l)
  for n in matches:
   before=[h for h in heads if h['line']<=n]
   if not before:stats['unsectioned_matches']+=1;continue
   h=before[-1]
   if admin.search(h['title']):stats['rejected_administrative_matches']+=1;continue
   stop=next((x for x in heads if x['line']>h['line'] and x['level']<=h['level']),{'line':len(lines)+1,'byte':len(b)})
   rec={'path':f.as_posix(),'heading':h['title'],'start_line':h['line'],'stop_line_exclusive':stop['line'],'start_byte':h['byte'],'stop_byte':stop['byte'],'match_line':n,'file_sha256':hashlib.sha256(b).hexdigest()}
   if not any(x['path']==rec['path'] and x['start_byte']==rec['start_byte'] for x in records):records.append(rec)
result={'guards_sha256':hashlib.sha256((R/'private/guards.json').read_bytes()).hexdigest(),'queries':queries,'roots':[x.as_posix() for x in roots],'stats':stats,'candidates':records,'limits':'One prospective guarded pass. No complete clearance; substring guards omit useful originals; opaque aliases may remain. JSON and other UTF8 sizes unrestricted. Administrative and unsectioned matches not displayed.'}
(R/'private/history-navigation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'stats':stats,'candidates':records},indent=2))
