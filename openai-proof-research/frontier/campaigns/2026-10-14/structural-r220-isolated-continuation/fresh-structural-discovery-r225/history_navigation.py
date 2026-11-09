from pathlib import Path
import os,fnmatch,re,json,hashlib
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r225')
g=json.loads((R/'guards.json').read_text())
def blocked(path):
 s=path.as_posix().casefold()
 return any(fnmatch.fnmatchcase(s,p) for p in g['wildcards']) or any(x in s for x in g['substrings']) or any(re.match(p,c) for c in s.split('/') for p in g['component_regexes'])
query=re.compile(r'Solomon[\s–—-]+Yau|Lorentz[\s-]+distance|two[\s-]+sided curvature maximum|Clifford.{0,70}(?:minimal hypersurface|Jacobi|volume|least.area|nullity)|(?:minimal hypersurface|spherical minimal immersion).{0,70}(?:near.equality|multiplicity|cone family)|least[\s-]+volume sweepout',re.I)
admin=re.compile(r'status|provenance|scope.and.evidence|contribution.screen|acceptance|disposition|handoff|summary|administrativ|catalog|read.extent|selection|source.inventory|prior.art|bibliograph',re.I)
head=re.compile(r'^(#{1,6})\s+(.+)$|^\\((?:sub)*section)\*?\{([^}]+)\}')
rows=[];counts={'directories':0,'pruned_directories':0,'pruned_files':0,'eligible_files':0,'utf8_files':0,'non_utf8_files':0,'candidate_sections':0,'administrative_headings_rejected':0};fail=[]
def walk(d):
 counts['directories']+=1
 with os.scandir(d) as entries:
  for e in entries:
   p=Path(e.path)
   if e.is_symlink():continue
   if blocked(p):counts['pruned_directories' if e.is_dir(follow_symlinks=False) else 'pruned_files']+=1;continue
   if e.is_dir(follow_symlinks=False):yield from walk(p)
   elif e.is_file(follow_symlinks=False):yield p
for p in walk(Path('.')):
 counts['eligible_files']+=1
 try:b=p.read_bytes();s=b.decode('utf8')
 except UnicodeDecodeError:counts['non_utf8_files']+=1;continue
 except OSError as e:fail.append({'path':p.as_posix(),'error':str(e)});continue
 counts['utf8_files']+=1
 lines=b.splitlines(keepends=True);offsets=[0];heads=[]
 for n,l in enumerate(lines):
  offsets.append(offsets[-1]+len(l));t=l.decode('utf8').rstrip();h=head.match(t)
  if h:heads.append((n,len(h[1]) if h[1] else 1+h[3].count('sub'),h[2] or h[4]))
 sections={}
 for n,l in enumerate(lines):
  if not query.search(l.decode('utf8')):continue
  preceding=[h for h in heads if h[0]<=n]
  h=preceding[-1] if preceding else (0,0,'[NO CLASSIFIED HEADING]')
  if admin.search(h[2]):counts['administrative_headings_rejected']+=1;continue
  end=next((hh[0] for hh in heads if hh[0]>h[0] and hh[1]<=h[1]),len(lines))
  key=(h[0],end,h[2]);sections.setdefault(key,[]).append(n+1)
 for (start,end,title),hits in sections.items():
  rows.append({'path':p.as_posix(),'heading':title,'lines':[start+1,end],'bytes':[offsets[start],offsets[end]],'hit_lines':hits,'body_displayed':False,'sha256_file':hashlib.sha256(b).hexdigest()})
counts['candidate_sections']=len(rows)
(R/'private').mkdir(exist_ok=True)
(R/'private/history-candidates.json').write_text(json.dumps({'query':query.pattern,'counts':counts,'failures':fail,'sections':rows},indent=2)+'\n')
print(json.dumps({'counts':counts,'failures':fail,'candidates':rows},indent=2))
