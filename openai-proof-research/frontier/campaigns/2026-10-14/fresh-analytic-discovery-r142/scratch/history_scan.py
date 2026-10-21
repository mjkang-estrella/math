from pathlib import Path
import os,fnmatch,json,re,hashlib
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
R=P/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r142'
ACTIVE=['*arithmetic*r112*','*structural*r147*','*arithmetic*r113*','*structural*r148*']
RECENT=['*analytic*r141*','*analytic*r140*','*analytic*r139*','*structural*r146*','*structural*r145*','*arithmetic*r111*','*arithmetic*r110*','*arithmetic*r109*','*arithmetic*r108*','*arithmetic*r107*','*analytic*r138*','*structural*r144*','*structural*r143*','*analytic*r137*','*analytic*r136*','*analytic*r135*','h138-*','t185r144-*','t177c143-*','t373e135-*','k369r134-*','t088p133-*']
ROLES=['*'+s+'*' for s in ['corpus','source','primary','history','search','inventor','fixture','control','extract','render','vendor','build','copy','copied','frozen','role','formal','manuscript','release','parent','literature','recovery','recover','context','catalog','packet','snapshot','worktree','node_modules','.git','venv','scratch','download','cache','raw','intake','brief','prompt','dispatch','task','seal','manifest','authentication','membership','provenance','acquisition','transcript','log','hits','scan','work','archive']]
# Exact word exceptions are intentionally absent: conservative coarse omissions are disclosed.
PATTERNS=ACTIVE+RECENT+ROLES+['*analytic*r142*']
def rejected(s): return any(fnmatch.fnmatchcase(s.lower(),pat) for pat in PATTERNS)
roots=['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','iterations','experiments','proposals','scouts','notes','findings']
rx=re.compile(r'(?i)(\b(?:source|theorem|result|T|I)\s*0?93\b|subgaussian.{0,60}log.?concav|log.?concav.{0,60}subgaussian|logarithmic.?sobolev|log.sobolev|stochastic localization|tilt.stab|tilted.{0,30}covariance)')
res=[]; stats={'read_utf8':0,'non_utf8_or_nul':0,'errors':[],'symlinks':0,'absent_roots':[],'pruned_count':0}; pruned=[]
for relroot in roots:
 root=P/relroot
 if not root.is_dir(): stats['absent_roots'].append(relroot); continue
 if any(rejected(c) for c in Path(relroot).parts): continue
 for base,dirs,files in os.walk(root,topdown=True,followlinks=False):
  kept=[]
  for d in sorted(dirs):
   q=Path(base)/d
   if rejected(d) or q.is_symlink():
    pruned.append(str(q.relative_to(P))); stats['symlinks']+=int(q.is_symlink())
   else: kept.append(d)
  dirs[:]=kept
  for f in sorted(files):
   q=Path(base)/f
   if rejected(f): pruned.append(str(q.relative_to(P))); continue
   if q.is_symlink(): stats['symlinks']+=1; continue
   try:
    b=q.read_bytes()
    if b'\0' in b: stats['non_utf8_or_nul']+=1; continue
    s=b.decode('utf8')
   except UnicodeError: stats['non_utf8_or_nul']+=1; continue
   except OSError as e: stats['errors'].append([str(q.relative_to(P)),str(e)]); continue
   stats['read_utf8']+=1
   matches=[{'line':i,'text':line} for i,line in enumerate(s.splitlines(),1) if rx.search(line)]
   if matches: res.append({'path':str(q.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matches':matches})
stats['pruned_count']=len(pruned)
(R/'private/history-scan.json').write_text(json.dumps({'project':str(P),'roots':roots,'component_patterns':PATTERNS,'regex':rx.pattern,'stats':stats,'hits':res,'pruned':pruned},indent=2))
print(json.dumps(stats)); print('MATCHED',len(res))
for h in res: print(h['path'],h['size'],[(m['line'],m['text'][:180]) for m in h['matches']][:8])
