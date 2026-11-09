from pathlib import Path
import os,json,fnmatch,subprocess,re,hashlib
P=Path.cwd();R=P/'frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r222'
g=json.loads((R/'guards.json').read_text());assert len(g['wildcards'])==367 and len(g['substrings'])==162
for f,a,b in [('analytic',144,195),('arithmetic',116,168),('structural',151,222)]:
 for n in range(a,b+1):assert f'*{f}*r{n}*' in g['wildcards'] and f'*{f}*{n}*' in g['wildcards']
for p in ['*k369r134-*','*k369134-*','*t185r144-*','*t185144-*']:assert p in g['wildcards']
def denied(rel):
 q=rel.casefold()
 return q==g['own_root'].casefold() or q.startswith(g['own_root'].casefold()+'/') or any(fnmatch.fnmatchcase(q,w) for w in g['wildcards']) or any(x in q for x in g['substrings']) or any(fnmatch.fnmatchcase(c,w) for c in q.split('/') for w in g['extra_component_patterns'])
files=[];pruned=0
# Walk only plausible authored containers; no ancestor or sibling-root inventory.
roots=['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','campaigns','iterations','experiments','proposals','scouts','notes','findings']
def walk(p):
 global pruned
 if denied(p.relative_to(P).as_posix()):pruned+=1;return
 try:entries=os.scandir(p)
 except FileNotFoundError:return
 with entries:
  for e in entries:
   q=Path(e.path);rel=q.relative_to(P).as_posix()
   if denied(rel):pruned+=1;continue
   if e.is_symlink():continue
   if e.is_dir(follow_symlinks=False):walk(q)
   elif e.is_file(follow_symlinks=False):files.append(rel)
for x in roots:walk(P/x)
pat=r'(stationary[ -]+integral[ -]+varifolds?|varifold[ -]+density[ -]+cent(?:er|re)s?|cent(?:er|re)ed[ -]+normal[ -]+blow[ -]?up|varifold[ -]+fitting[ -]+frequency|linearized[ -]+varifold[ -]+measures?|singular[ -]set[ -]+dimension[ -]+reduction|excess[ -]+contact[ -]+packing|almost[ -]everywhere[ -]+minimal[ -]+regularity|height[ -]and[ -]stress|height[ -]stress[ -]+measure|signed[ -]excess|stationary[ -]+Lipschitz[ -]+graphs?|varifold.{0,45}quantitative[ -]+stratification)'
hits=[]
for a in range(0,len(files),150):
 p=subprocess.run(['rg','--files-with-matches','--ignore-case','--text','--multiline','--',pat,*files[a:a+150]],capture_output=True,text=True)
 assert p.returncode in [0,1],p.stderr
 hits.extend(p.stdout.splitlines())
rows=[]
rx=re.compile(pat,re.I);heading=re.compile(r'^(#{1,6})\s+(.+)|^\\((?:sub)*section)\*?\{([^}]+)\}',re.M)
for rel in hits:
 assert not denied(rel)
 b=(P/rel).read_bytes()
 try:t=b.decode('utf-8')
 except UnicodeDecodeError:rows.append({'path':rel,'excluded_body':'not UTF8'});continue
 hs=list(heading.finditer(t)); matches=list(rx.finditer(t));selected={}
 for m in matches:
  prior=[h for h in hs if h.start()<=m.start()];h=prior[-1] if prior else None
  title=(h.group(2) or h.group(4)) if h else '[unheaded; no automatic body admission]'
  selected[title]=selected.get(title,0)+1
 rows.append({'path':rel,'matched_headings':selected,'body_admitted':False})
D={'guards_sha256':hashlib.sha256((R/'guards.json').read_bytes()).hexdigest(),'eligible_file_count':len(files),'pruned_entry_count':pruned,'query':pat,'rows':rows,'limitations':'Path pruning and heading navigation only. All matching bodies require mathematical/original classification before display; opaque aliases may escape, coarse omissions remain; excluded peers not read.'}
(R/'private/history-navigation.json').write_text(json.dumps(D,indent=2)+'\n');print(json.dumps(D,indent=2))
