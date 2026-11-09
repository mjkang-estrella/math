from pathlib import Path
import os,fnmatch,json,re,hashlib
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r238')
g=json.loads((R/'guards.json').read_text())
assert len(g['wildcards'])==399 and len(g['substrings'])==162
assert all(x in g['wildcards'] for x in ['*k369r134-*','*k369134-*','*t185r144-*','*t185144-*','*structural*r238*','*structural*238*'])
def banned(p):
 s=p.as_posix().casefold()
 return any(fnmatch.fnmatchcase(s,w) for w in g['wildcards']) or any(x in s for x in g['substrings']) or any(fnmatch.fnmatchcase(c,w) for c in p.parts for w in g['additional_component_patterns'])
queries=[
 r'hard[ -]sphere.{0,100}(?:local conservation|nonuniqueness|entropy (?:balance|equality|defect))',
 r'boltzmann.{0,100}(?:cold jets?|cap dilation|nonconcentration|entropy (?:equality|balance|defect)|logarithmic collision)',
 r'kinetic.{0,35}entropy.{0,40}(?:branch|separation)',
 r'periodic.{0,35}collision.{0,35}(?:prepared.state|gluing)',
 r'five[ -]gain.{0,35}(?:rank|pullback|submersion)',
 r'cold.{0,12}jets?.{0,40}(?:retirement|bath)',
 r'gain.small.mass.{0,60}(?:boltzmann|collision|entropy)'
]
rx=[re.compile(q,re.I) for q in queries]
auth=re.compile(r'(?:^|/)(?:campaigns|iterations|experiments|proposals|scouts|notes|findings)(?:/|[-_.])',re.I)
heading=re.compile(rb'^(#{1,6})[ \t]+(.+)$')
admin=re.compile(r'status|provenance|scope.and.evidence|contribution.screen|handoff|disposition|administrat|acceptance|count|catalog|intake|registry|reading|evidence|source.access',re.I)
counts=dict(directories_pruned=0,files_pruned=0,eligible_utf8=0,nonutf8=0,matched_files=0)
hits=[]
for d,dirs,files in os.walk('.',topdown=True,followlinks=False):
 base=Path(d)
 keep=[]
 for n in dirs:
  p=base/n
  if p.is_symlink() or banned(p):counts['directories_pruned']+=1
  else:keep.append(n)
 dirs[:]=sorted(keep)
 for n in sorted(files):
  p=base/n
  if p.is_symlink() or banned(p):counts['files_pruned']+=1;continue
  if not auth.search(p.as_posix()):continue
  b=p.read_bytes()
  try:t=b.decode('utf-8')
  except UnicodeDecodeError:counts['nonutf8']+=1;continue
  counts['eligible_utf8']+=1
  if not any(q.search(t) for q in rx):continue
  counts['matched_files']+=1
  lines=b.splitlines(keepends=True);offsets=[0]
  for l in lines:offsets.append(offsets[-1]+len(l))
  hs=[]
  for j,l in enumerate(lines):
   m=heading.match(l.rstrip(b'\r\n'))
   if m:hs.append((j,len(m[1]),m[2].decode()))
  for j,l in enumerate(lines):
   s=l.decode()
   qi=[k for k,q in enumerate(rx) if q.search(s)]
   if not qi:continue
   prev=[h for h in hs if h[0]<=j]
   h=prev[-1] if prev else (0,0,'[unclassified no heading]')
   ends=[z[0] for z in hs if z[0]>h[0] and z[1]<=h[1]]
   end=ends[0] if ends else len(lines)
   item=dict(path=p.as_posix(),sha256=hashlib.sha256(b).hexdigest(),hit_line=j+1,heading_line=h[0]+1,heading=h[2],start_byte=offsets[h[0]],end_byte=offsets[end],end_line_exclusive=end+1,query_ids=qi,classification='reject-administrative' if admin.search(h[2]) else 'unclassified' if h[1]==0 else 'candidate-mathematical')
   hits.append(item)
record={'pass':'single prospective compound navigation, no mathematical body displayed','queries':queries,'counts':counts,'hits':hits,'limits':'All guards applied before descent/read/decode. No file-size cutoff; hidden and ignored names treated normally. Coarse exclusions and opaque aliases preclude exhaustive clearance. Matching body lines processed for navigation but not displayed or admitted as proof.'}
(R/'private/original-navigation.json').write_text(json.dumps(record,indent=2))
print(json.dumps({'counts':counts,'hits':hits},indent=2))
