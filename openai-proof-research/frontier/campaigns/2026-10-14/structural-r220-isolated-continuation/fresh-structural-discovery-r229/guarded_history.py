from pathlib import Path
import os,json,fnmatch,re,hashlib
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r229');G=json.loads((R/'guards.json').read_text())
def denied(p):
 s=p.as_posix().casefold()
 return s==G['own_root'].casefold() or s.startswith(G['own_root'].casefold()+'/') or any(fnmatch.fnmatchcase(s,w) for w in G['wildcards']+G['derivative_wildcards']) or any(v in s for v in G['substrings'])
qs=[r'affine[ -]+bernstein',r'affine[ -]+maximal.{0,40}(?:ten|dimension|radial|graph)',r'berwald.{0,15}blaschke',r'thin[ -]+slice.{0,30}affine',r'nonquadratic.{0,30}affine[ -]+maximal',r'invariant[ -]+box.{0,40}(?:radial|affine)',r'(?:logarithmic[ -]+cell|centered[ -]+fibers|support[ -]+coordinates).{0,50}(?:affine|tube)',r'trudinger.{0,20}wang',r'9/2.{0,60}33/7',r'(?:affine[ -]+metric|affine[ -]+complete).{0,50}(?:radial|nonquadratic|dimension)']
query=re.compile('|'.join(qs),re.I)
admin=re.compile(r'status|provenance|scope.*evidence|contribution.*screen|acceptance|disposition|handoff|summary|receipt|catalog|inventory|reading|sources|literature|history|evidence|references|administrative|candidate.*screen',re.I)
heading=re.compile(r'^(#{1,6})\s+(.+)|^\\((?:sub)*section)\*?\{([^}]+)')
counts={'eligible_utf8_files':0,'eligible_bytes':0,'non_utf8':0,'pruned_entries':0,'matched_files':0,'rejected_admin_sections':0,'unheaded_matches':0}
hits=[]
def walk(p):
 if denied(p):counts['pruned_entries']+=1;return
 if not p.exists() or p.is_symlink():return
 if p.is_dir():
  with os.scandir(p) as it:
   for e in it:
    q=p/e.name
    if denied(q):counts['pruned_entries']+=1;continue
    if e.is_symlink():continue
    if e.is_dir(follow_symlinks=False):walk(q)
    elif e.is_file(follow_symlinks=False):read(q)
 else:read(p)
def read(p):
 assert not denied(p)
 b=p.read_bytes()
 try:s=b.decode('utf-8')
 except UnicodeDecodeError:counts['non_utf8']+=1;return
 counts['eligible_utf8_files']+=1;counts['eligible_bytes']+=len(b)
 if not query.search(s):return
 counts['matched_files']+=1
 ls=b.splitlines(keepends=True);off=[0];hs=[]
 for i,l in enumerate(ls):
  off.append(off[-1]+len(l));m=heading.match(l.decode('utf8'))
  if m:hs.append((i,len(m[1]) if m[1] else (1+m[3].count('sub')),m[2] or m[4]))
 chosen=set()
 for i,l in enumerate(ls):
  if not query.search(l.decode('utf8')):continue
  before=[h for h in hs if h[0]<=i]
  if not before:counts['unheaded_matches']+=1;continue
  h=before[-1]
  if admin.search(h[2]):counts['rejected_admin_sections']+=1;continue
  end=next((x[0] for x in hs if x[0]>h[0] and x[1]<=h[1]),len(ls))
  key=(h[0],end)
  if key in chosen:continue
  chosen.add(key)
  hits.append({'path':p.as_posix(),'heading':h[2],'lines':[h[0]+1,end],'bytes':[off[h[0]],off[end]],'full_sha256':hashlib.sha256(b).hexdigest()})
for p in ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','campaigns','iterations','experiments','proposals','scouts','notes','findings']:walk(Path(p))
(R/'private/history-navigation.json').write_text(json.dumps({'queries':qs,'counts':counts,'candidates':hits,'limits':'Guarded narrow navigation only; no exhaustive history clearance; headings classified before bodies.'},indent=2)+'\n')
print(json.dumps(counts));print(json.dumps(hits,indent=2))
