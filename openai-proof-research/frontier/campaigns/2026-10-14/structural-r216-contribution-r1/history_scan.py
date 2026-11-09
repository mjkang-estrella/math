import os,sys,json,fnmatch,re,hashlib
from pathlib import Path
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN=ROOT/'frontier/campaigns/2026-10-14/structural-r216-contribution-r1'
g=json.loads((OWN/'packet/private/guards.json').read_text())
assert len(g['wildcards'])==355 and len(g['substrings'])==162
patterns=g['wildcards']+g['derivatives']
def blocked(rel):
 p=rel.casefold()
 return any(fnmatch.fnmatchcase(p,x) for x in patterns) or any(x in p for x in g['substrings'])
for cat,a,b in [('analytic',144,195),('arithmetic',116,168),('structural',151,216)]:
 for n in range(a,b+1):
  assert f'*{cat}*r{n}*' in patterns and f'*{cat}*{n}*' in patterns
for p in ['*k369r134-*','*k369134-*','*t185r144-*','*t185144-*']:assert p in patterns
assert blocked('frontier/campaigns/2026-10-14/structural-r216-correctness-r1/x')
assert blocked('frontier/campaigns/2026-10-14/structural-r216-contribution-r1/x')
queries=[r'natural[ -]coset',r'(?:separated[ -]double|doubl(?:ing|ed)[ -]partition)',r'homogeneous.{0,55}(?:partition|tube).{0,55}(?:comparison|suspension)',r'momentum[ -]separat(?:ed|ion).{0,60}lagrangian',r'regular[ -]band.{0,50}(?:cobordism|transport)',r'nearby.{0,15}exact.{0,15}lagrangian.{0,30}obstruction',r'cotangent.{0,20}zero[ -]section.{0,30}hamiltonian.{0,15}isotop',r'marked.{0,10}exact.{0,15}embedding',r'homogeneous.{0,35}generating.{0,25}family',r'Guillermou.{0,30}(?:trick|doubl)',r'Waldhausen.{0,30}(?:partition|tube)']
regex=re.compile('|'.join(queries),re.I)
admin=re.compile(r'(?:status|provenance|scope.and.evidence|contribution.screen|source.contract|stronger.companion|review|acceptance|reading|navigation|intake|disposition|history|handoff|source.truth)',re.I)
stats={'eligible_files':0,'utf8_files':0,'decoded_bytes':0,'pruned_directories':0,'pruned_files':0,'symlinks_skipped':0}
hits=[]
def visit(folder):
 with os.scandir(folder) as it:
  entries=sorted(it,key=lambda e:e.name)
 for e in entries:
  rel=Path(e.path).relative_to(ROOT).as_posix()
  if e.is_symlink():stats['symlinks_skipped']+=1;continue
  isdir=e.is_dir(follow_symlinks=False)
  if blocked(rel):stats['pruned_directories' if isdir else 'pruned_files']+=1;continue
  if isdir:visit(e.path);continue
  if not e.is_file(follow_symlinks=False):continue
  stats['eligible_files']+=1
  b=Path(e.path).read_bytes()
  try:t=b.decode('utf-8')
  except UnicodeDecodeError:continue
  stats['utf8_files']+=1;stats['decoded_bytes']+=len(b)
  lines=t.splitlines(keepends=True);heading='[no mathematical heading]';hoff=0;offset=0
  for i,l in enumerate(lines,1):
   if re.match(r'^#{1,6}\s|^\\(?:sub)*section\{',l):heading=l.strip();hoff=offset
   m=regex.search(l)
   if m:
    rejected=bool(admin.search(heading)) or heading=='[no mathematical heading]'
    hits.append({'path':rel,'line':i,'byte':offset,'heading_byte':hoff,'heading':heading if not admin.search(heading) else '[administrative heading rejected before body display]','matched_alias':m.group(0),'rejected':rejected,'file_sha256':hashlib.sha256(b).hexdigest()})
   offset+=len(l.encode('utf-8'))
visit(ROOT/'frontier')
result={'guards':{'wildcards':355,'substrings':162},'queries':queries,'stats':stats,'hits':hits,'semantic_body_reads':0,'limits':'One fresh narrow pass only. Pruned before descent/read/decode; no symlinks; no extension/size/hidden/ignored cutoff. Heading classification precedes any body selection. No exhaustive clearance or priority inference.'}
(OWN/'packet/private/history-scan.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
