import os,fnmatch,json,re,hashlib
from pathlib import Path
R=Path(__file__).resolve().parent;P=Path.cwd();g=json.loads((R/'private/guards.json').read_bytes())
assert len(g['wildcards'])==359 and len(g['substrings'])==162
patterns=[r'tamed[\s-]+to[\s-]+compatible',r'almost[\s-]+complex[\s-]+cohomology',r'(?:compatible|taming)[\s-]+symplectic[\s-]+cone',r'(?:invariant[\s-]+taming[\s-]+cone|prescribed[\s-]+class[\s-]+separation)',r'(?:closed[\s-]+anti[\s-]+invariant|anti[\s-]+invariant[\s-]+cohomology)',r'(?:fixed|prescribed)[\s-]+class[\s-]+(?:compatible|nonselection)',r'(?:compatible[\s-]+(?:form|family|representative)[^\n]{0,90}(?:changing|varying)[\s-]+(?:J|almost[\s-]+complex))',r'(?:positive[\s-]+density[\s-]+restriction|relative[\s-]+projection[\s-]+estimate)',r'(?:taming[\s-]+cone[^\n]{0,90}strict[\s-]+(?:dual[\s-]+)?positivity)']
queries=[re.compile(p,re.I) for p in patterns]
def blocked(p):
 s=p.as_posix().casefold()
 return any(fnmatch.fnmatchcase(s,x) for x in g['wildcards']+g['derivative_patterns']) or any(x in s for x in g['substrings'])
# Only explicitly named authored areas, never project root inventory or peer metadata.
starts=[Path('frontier')/x for x in ['campaigns','iterations','experiments','proposals','scouts','notes','findings']]
counts={'utf8':0,'non_utf8':0,'pruned_entries':0,'symlinks':0};hits=[]
def visit(rel):
 if blocked(rel):counts['pruned_entries']+=1;return
 p=P/rel
 if p.is_symlink():counts['symlinks']+=1;return
 if not p.exists():return
 if p.is_dir():
  with os.scandir(p) as it:
   for entry in it:
    child=rel/entry.name
    if blocked(child):counts['pruned_entries']+=1;continue
    if entry.is_symlink():counts['symlinks']+=1;continue
    visit(child)
 elif p.is_file():
  b=p.read_bytes()
  try:t=b.decode('utf-8')
  except UnicodeDecodeError:counts['non_utf8']+=1;return
  counts['utf8']+=1
  matched=[i for i,q in enumerate(queries) if q.search(t)]
  if not matched:return
  ll=b.splitlines(keepends=True);oo=[0]
  for l in ll:oo.append(oo[-1]+len(l))
  heads=[]
  for i,l in enumerate(ll,1):
   v=l.decode().strip();m=re.match(r'^(#{1,6})\s+(.+)',v)
   if m:heads.append((i,len(m[1]),m[2]))
   else:
    m=re.match(r'^\\(section|subsection|subsubsection)\*?\{([^}]*)\}',v)
    if m:heads.append((i,{'section':1,'subsection':2,'subsubsection':3}[m[1]],m[2]))
  candidates=[]
  for i,l in enumerate(ll,1):
   if not any(q.search(l.decode()) for q in queries):continue
   ancestors=[]
   for h in heads:
    if h[0]>i:break
    while ancestors and ancestors[-1][1]>=h[1]:ancestors.pop()
    ancestors.append(h)
   if ancestors:
    st,level,title=ancestors[-1];en=next((h[0]-1 for h in heads if h[0]>st and h[1]<=level),len(ll))
   else:st,en,title=1,len(ll),'[no classified mathematical heading]'
   entry={'heading':title,'ancestor_headings':[h[2] for h in ancestors],'lines':[st,en],'bytes':[oo[st-1],oo[en]],'match_line':i}
   if entry not in candidates:candidates.append(entry)
  hits.append({'path':rel.as_posix(),'sha256':hashlib.sha256(b).hexdigest(),'query_ids':matched,'candidates':candidates})
for start in starts:visit(start)
result={'roots':[s.as_posix() for s in starts],'patterns':patterns,'counts':counts,'candidates':hits,'coverage':'navigation only; no mathematical body displayed by this script; coarse omissions and opaque aliases remain'}
(R/'private/history-navigation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
