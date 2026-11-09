from pathlib import Path
import os,re,json,hashlib
from guard import rejected,validate,OWN
R=Path(OWN)
validate()
# Predicates are applied before descent and before byte reads, on full project-relative POSIX paths.
patterns=[r'cartan[\s~–—-]*hadamard',r'CAT\s*(?:\$|\\\()?\s*\(0\).{0,60}(?:integral|sharp|isoperimet|chord)',r'(?:sharp|integral).{0,50}fillings?\s+(?:in|of)\s+(?:proper\s+)?CAT',r'finite[ -]perimeter\s+profile\s+comparison',r'current\s+chord\s+inequalit',r'confined[ -]boundary\s+isoperimetr',r'conformally\s+weighted\s+chords',r'Euclidean\s+equality\s+rigidity',r'confined\s+isoperimetric\s+profile',r'quadratic\s+majorant\s+for\s+mass']
query=re.compile('|'.join(patterns),re.I)
admin=re.compile(r'(?:status|provenance|scope.and.evidence|contribution.screen|administrativ|disposition|handoff|acceptance|campaign.state|source.authentication|source.coverage|read.extents|source.selection)',re.I)
head=re.compile(r'(?m)^(#{1,6})\s+([^\n]+)$|^\\(section|subsection|subsubsection)\*?\{([^\n}]+)\}')
counts={'pruned_dirs':0,'pruned_files':0,'eligible_utf8':0,'binary_or_nonutf8':0,'symlinks_omitted':0}
hits=[]
def visit(d):
 with os.scandir(d) as it:
  for ent in sorted(it,key=lambda x:x.name.casefold()):
   p=Path(ent.path); rel=p.as_posix()
   if rel.startswith('./'): rel=rel[2:]
   if ent.is_symlink(): counts['symlinks_omitted']+=1; continue
   isdir=ent.is_dir(follow_symlinks=False)
   if rejected(rel):
    counts['pruned_dirs' if isdir else 'pruned_files']+=1;continue
   if isdir: visit(p);continue
   if not ent.is_file(follow_symlinks=False): continue
   # This is a candidate search, not semantic reading. No extension/size/hidden filters.
   assert not rejected(rel)
   b=p.read_bytes()
   try: t=b.decode('utf8')
   except UnicodeDecodeError: counts['binary_or_nonutf8']+=1;continue
   if '\0' in t: counts['binary_or_nonutf8']+=1;continue
   counts['eligible_utf8']+=1
   matches=list(query.finditer(t))
   if not matches:continue
   hs=list(head.finditer(t)); seen=set()
   for match in matches:
    prior=[h for h in hs if h.start()<=match.start()]
    if not prior:
     key=(0,len(t),'NO_HEADING: manual classification needed',0)
    else:
     h=prior[-1];level=len(h.group(1)) if h.group(1) else {'section':1,'subsection':2,'subsubsection':3}[h.group(3)]
     title=h.group(2) or h.group(4)
     following=[x for x in hs if x.start()>h.start() and (len(x.group(1)) if x.group(1) else {'section':1,'subsection':2,'subsubsection':3}[x.group(3)])<=level]
     key=(h.start(),following[0].start() if following else len(t),title,level)
    if key in seen:continue
    seen.add(key);a,z,title,level=key
    x={'path':rel,'sha256':hashlib.sha256(b).hexdigest(),'file_bytes':len(b),'heading':title,'start':len(t[:a].encode()),'end':len(t[:z].encode()),'classification':'reject-administrative' if admin.search(title) else ('needs-heading-classification' if not level else 'candidate-math-heading'),'query_alias':match.group(0)}
    hits.append(x)
visit(Path('.'))
(R/'private/original-candidates.json').write_text(json.dumps(hits,indent=2)+'\n')
(R/'private/original-navigation-counts.json').write_text(json.dumps({'guards':validate(),'counts':counts,'queries':patterns,'limits':'No exhaustive clearance: coarse substring omissions and opaque aliases possible. Candidate displays are headings only. No excluded namespace admitted.'},indent=2)+'\n')
print(json.dumps({'counts':counts,'candidate_sections':len(hits)},indent=2))
for i,x in enumerate(hits):
 print(json.dumps({'id':i,**{k:x[k] for k in ['path','heading','start','end','classification','query_alias']}},ensure_ascii=False))
