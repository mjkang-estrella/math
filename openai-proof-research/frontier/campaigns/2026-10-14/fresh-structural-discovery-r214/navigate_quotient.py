from pathlib import Path
import os,re,json,fnmatch,hashlib
R=Path("frontier/campaigns/2026-10-14/fresh-structural-discovery-r214")
g=json.loads((R/"GUARDS.json").read_text())
patterns=g["wildcards"];subs=g["substrings"]
rx=[re.compile(x) for x in g["derivative_component_regexes"]]
def excluded(path):
 p=path.as_posix().casefold()
 return p==g["own_root"] or p.startswith(g["own_root"]+"/") or any(x in p for x in subs) or any(fnmatch.fnmatchcase(p,x) for x in patterns) or any(r.match(part) for r in rx for part in p.split('/'))
queries=[r'non[ -]?autonomous.{0,100}(?:equivariant|weighted\s+quotient)',r'(?:equivariant|weighted\s+quotient).{0,100}non[ -]?autonomous',r'quotient\s+(?:straighten|lineariz|normaliz).{0,100}(?:overshear|circle\s+action|bisectional)',r'(?:overshear|circle\s+action).{0,100}quotient\s+(?:straighten|lineariz|normaliz)',r'equivariant.{0,60}constant[ -]volume.{0,40}jet',r'fixed[ -]locus.{0,100}(?:shrinking\s+chart|positive\s+bisectional)',r'positive\s+bisectional.{0,100}fixed[ -]locus']
q=[re.compile(x,re.I|re.S) for x in queries]
admin=re.compile(r'status|provenance|scope\s*(?:and|&)\s*evidence|contribution[ -]screen|administrativ|disposition|handoff|acceptance|reading|retrieval|authentication|metadata|manifest|summary|final|report|audit|review',re.I)
counts={'directories_pruned':0,'files_pruned':0,'symlinks_skipped':0,'utf8_files_read':0,'nonutf8_skipped':0,'admin_sections_rejected':0,'candidate_sections':0}
found=[]
def process(p):
 if p.name.casefold()=='agents.md':return
 b=p.read_bytes()
 try:s=b.decode('utf-8')
 except UnicodeDecodeError:counts['nonutf8_skipped']+=1;return
 counts['utf8_files_read']+=1
 matches=[m for x in q for m in x.finditer(s)]
 if not matches:return
 # Heading metadata only before any selected body display.
 heads=[]
 for m in re.finditer(r'(?m)^(#{1,6})[ \t]+(.+)$|^\\(subsubsection|subsection|section|chapter)\*?\{([^\n]*)\}',s):
  level=len(m.group(1)) if m.group(1) else {'chapter':1,'section':2,'subsection':3,'subsubsection':4}[m.group(3)]
  heads.append((m.start(),m.end(),level,m.group(2) or m.group(4)))
 seen=set()
 for m in matches:
  before=[h for h in heads if h[0]<=m.start()]
  if not before:
   heading='[unsectioned: requires explicit classification]';start=0;end=len(s);level=0;parents=[]
  else:
   h=before[-1];start=h[0];heading=h[3];level=h[2]
   end=next((x[0] for x in heads if x[0]>start and x[2]<=level),len(s))
   parents=[];limit=level
   for x in reversed(before[:-1]):
    if x[2]<limit:parents.append(x[3]);limit=x[2]
  if (start,end) in seen:continue
  seen.add((start,end))
  if admin.search(heading) or any(admin.search(x) for x in parents):counts['admin_sections_rejected']+=1;continue
  a=len(s[:start].encode());z=len(s[:end].encode())
  found.append({'path':p.as_posix(),'heading':heading,'parents':parents,'start':a,'stop':z,'file_bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matched_queries':[queries[i] for i,x in enumerate(q) if x.search(s[start:end])],'classification':'candidate heading only; body not yet displayed'})
def walk(d):
 if excluded(d):counts['directories_pruned']+=1;return
 if not d.is_dir():return
 for e in os.scandir(d):
  p=Path(e.path)
  if e.is_symlink():counts['symlinks_skipped']+=1;continue
  if excluded(p):counts['directories_pruned' if e.is_dir(follow_symlinks=False) else 'files_pruned']+=1;continue
  if e.is_dir(follow_symlinks=False):walk(p)
  elif e.is_file(follow_symlinks=False):process(p)
roots=[Path('frontier')/x for x in ('campaigns','iterations','experiments','proposals','scouts','notes','findings')]
for p in roots:walk(p)
counts['candidate_sections']=len(found)
record={'roots':[x.as_posix() for x in roots],'queries':queries,'counts':counts,'candidates':found,'limits':'No ancestor inventory; no shared coordination or peer status read. No size or extension cutoff. Hidden/ignored files eligible after pruning. Unsectioned files not admitted semantically. Coarse omissions and opaque false admissions possible; no exhaustive clearance.'}
(R/'private/quotient-navigation.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'counts':counts,'candidates':found},indent=2))
