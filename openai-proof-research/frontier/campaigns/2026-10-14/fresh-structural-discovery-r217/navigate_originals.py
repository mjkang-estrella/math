from pathlib import Path
import os,fnmatch,re,json,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r217');G=json.loads((R/'isolation.json').read_text())
def excluded(path):
 p=path.casefold()
 return p==str(R).casefold() or p.startswith(str(R).casefold()+'/') or any(fnmatch.fnmatchcase(p,x) for x in G['wildcards']+G['derivative_patterns']) or any(s in p for s in G['substrings'])
queries=[r'hypersymplectic',r'hyperk(?:a|ä|\\\"a|&auml;)hler[ -]+triple',r'positive[ -]+closed[ -]+triple',r'coefficient[ -]+sphere',r'definite[ -]+pair.{0,80}(?:taming|current|pencil)',r'density[ -]+weight.{0,30}closed',r'exact[ -]+form[ -]+inverse',r'lattice[ -]+chamber']
q=re.compile('|'.join(queries),re.I)
heading=re.compile(r'^(#{1,6})\s+(.+)$|^\\(section|subsection|subsubsection|chapter)(?:\*)?\{([^}]+)\}',re.M)
admin=re.compile(r'status|provenance|scope.{0,15}evidence|contribution.{0,20}screen|screen.{0,20}contribution|administrat|handoff|intake|inventory|catalog|brief|metadata|reading|read limits|source map|literature|campaign|coordination|authentication|acceptance|summary|disposition',re.I)
candidates=[];counts={'directories_pruned':0,'files_pruned':0,'eligible_files_read':0,'utf8_files':0,'utf8_bytes':0,'non_utf8':0,'symlinks_skipped':0,'matched_files':0,'unclassified_matches':0,'admin_matches_rejected':0}
for folder,dirs,files in os.walk('.',topdown=True,followlinks=False):
 rel=Path(folder).as_posix().removeprefix('./')
 def full(n):return n if rel=='.' else rel+'/'+n
 keep=[]
 for n in dirs:
  p=full(n)
  if excluded(p):counts['directories_pruned']+=1
  elif Path(p).is_symlink():counts['symlinks_skipped']+=1
  else:keep.append(n)
 dirs[:]=keep
 for n in files:
  p=full(n)
  if excluded(p):counts['files_pruned']+=1;continue
  if Path(p).is_symlink():counts['symlinks_skipped']+=1;continue
  try:b=Path(p).read_bytes()
  except (OSError,PermissionError):continue
  counts['eligible_files_read']+=1
  try:t=b.decode('utf8')
  except UnicodeDecodeError:counts['non_utf8']+=1;continue
  counts['utf8_files']+=1;counts['utf8_bytes']+=len(b)
  hits=list(q.finditer(t))
  if not hits:continue
  counts['matched_files']+=1; hs=list(heading.finditer(t));seen=set()
  for m in hits:
   before=[h for h in hs if h.start()<=m.start()]
   if not before:counts['unclassified_matches']+=1;continue
   h=before[-1]; title=h.group(2) or h.group(4)
   if admin.search(title):counts['admin_matches_rejected']+=1;continue
   if h.start() in seen:continue
   seen.add(h.start());lev=len(h.group(1)) if h.group(1) else {'chapter':0,'section':1,'subsection':2,'subsubsection':3}[h.group(3)]
   end=len(t)
   for hh in hs:
    if hh.start()<=h.start():continue
    ll=len(hh.group(1)) if hh.group(1) else {'chapter':0,'section':1,'subsection':2,'subsubsection':3}[hh.group(3)]
    if ll<=lev:end=hh.start();break
   candidates.append({'path':p,'heading':title,'match':m.group(0),'bytes':[len(t[:h.start()].encode()),len(t[:end].encode())],'file_sha256':hashlib.sha256(b).hexdigest(),'heading_classification':'pending semantic eligibility; no body displayed'})
(R/'private/original-navigation.json').write_text(json.dumps({'queries':queries,'counts':counts,'candidates':candidates,'limits':'No size cutoff, hidden/ignored/JSON/tex/bib eligible after guards. No binary decoding; symlinks skipped. Coarse aliases may omit originals; opaque aliases may escape. No exhaustive or priority clearance.'},indent=2)+'\n')
print(json.dumps({'counts':counts,'candidates':candidates},indent=2))
