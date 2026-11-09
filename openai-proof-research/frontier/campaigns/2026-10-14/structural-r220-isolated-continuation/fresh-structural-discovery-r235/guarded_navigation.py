from pathlib import Path
import os,fnmatch,re,json,hashlib
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r235')
g=json.loads((R/'guards.json').read_text()); pats=g['full_path_casefold_wildcards']; subs=g['full_path_casefold_substrings']
assert len(pats)==393 and len(subs)==162
for p in pats:
 if '*r' in p: assert p.replace('*r','*') in pats
assert '*k369134-*' in pats and '*t185144-*' in pats
rx=[re.compile(p) for p in g['extra_component_regexes']]
def exclude(p):
 p=p.casefold()
 return p.startswith(R.as_posix().casefold()) or any(s in p for s in subs) or any(fnmatch.fnmatchcase(p,q) for q in pats) or any(r.fullmatch(c) for c in p.split('/') for r in rx)
queries=[r'negatively[ -]pinched.{0,50}(?:k[aä](?:hler|ehler)|bounded holomorphic)',r'one.sided negative.{0,80}(?:holomorphic|liouville)',r'Hartogs.{0,90}(?:mixed|sectional|pinch)',r'pluriharmonic minorant',r'positive representing densit',r'logarithmic (?:density )?tests.{0,80}(?:base|potential)',r'quiet.{0,50}(?:fiber profile|radial tube|tube assembly)',r'phases separate low.degree jets',r'bounded holomorphic coordinates',r'weighted holomorphic.{0,80}(?:section|algebra)',r'(?:Hilbert|tensor).{0,60}(?:bounded holomorphic|Hartogs)']
q=re.compile('|'.join(queries),re.I)
admin=re.compile(r'status|provenance|scope.and.evidence|contribution.screen|acceptance|disposition|handoff|reading|references|bibliography|navigation|audit|manifest',re.I)
counts={'pruned_dirs':0,'pruned_files':0,'eligible_utf8_files':0,'binary_or_nonutf8':0,'symlinks_skipped':0}; matches=[]
def walk(d):
 for entry in os.scandir(d):
  p=Path(entry.path).as_posix(); p=p[2:] if p.startswith('./') else p
  if exclude(p):
   counts['pruned_dirs' if entry.is_dir(follow_symlinks=False) else 'pruned_files']+=1;continue
  if entry.is_symlink():counts['symlinks_skipped']+=1;continue
  if entry.is_dir(follow_symlinks=False):walk(p);continue
  if not entry.is_file(follow_symlinks=False):continue
  b=Path(p).read_bytes()
  if b'\0' in b:counts['binary_or_nonutf8']+=1;continue
  try:s=b.decode('utf8')
  except UnicodeDecodeError:counts['binary_or_nonutf8']+=1;continue
  counts['eligible_utf8_files']+=1
  if not q.search(s):continue
  lines=b.splitlines(keepends=True); offset=0; heading='[unsectioned]';level=0; hs=0;hits=[]
  heads=[]
  for i,l in enumerate(lines):
   t=l.decode(); md=re.match(r'^(#{1,6})\s+(.+)',t);tex=re.match(r'\\((?:sub)*section)\*?\{([^}]+)',t)
   if md:heads.append((i,offset,len(md[1]),md[2]))
   if tex:heads.append((i,offset,1+tex[1].count('sub'),tex[2]))
   offset+=len(l)
  for m in q.finditer(s):
   # consistent bytes parser: match byte coordinate, not str.splitlines
   bo=len(s[:m.start()].encode()); prev=[h for h in heads if h[1]<=bo]
   h=prev[-1] if prev else (0,0,0,'[unsectioned]')
   ends=[x for x in heads if x[1]>h[1] and x[2]<=h[2]] if h[2] else []
   en=ends[0][1] if ends else len(b)
   hit={'heading':h[3],'section_bytes':[h[1],en],'match_byte':bo,'matched_alias':m.group(0),'classification':'reject administrative' if admin.search(h[3]) else 'candidate requires overlap classification'}
   if hit not in hits:hits.append(hit)
  matches.append({'path':p,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'hits':hits})
walk('.')
record={'pass':1,'queries':queries,'guards_sha256':hashlib.sha256((R/'guards.json').read_bytes()).hexdigest(),'counts':counts,'matches':matches,'limits':'No exhaustive clearance. Broad path guards omit useful originals; opaque aliases may escape. Candidate headings only are displayed, never administrative or unclassified bodies. No filesize cutoff; all eligible UTF8 file types considered.'}
out=R/'private/history-navigation-01.json';assert not out.exists();out.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
