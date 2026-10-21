from pathlib import Path
import os,re,json,hashlib
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OUT=ROOT/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r144'
# Match every component, including filenames; prune before descent/open.
ACTIVE=re.compile(r'analytic.*r13[78]|t177c143-|structural.*r143|analytic.*r13[56]|arithmetic.*r10[789]|t373e135-|k369r134-|t088p133-|structural.*r144',re.I)
DERIV=re.compile(r'(^|[-_.])(inputs?|copies|copy|copied|corpus|fixtures?|controls?|sources?|renders?|vendor|frozen|outside|archives?|inventory|inventories|payload|release|snapshot|snapshots|intakes?|reviews?|proof-review|contribution|manuscript|publication|formal|fetched|history|catalogue|catalog|inventory|corpus|active|running|pending|node_modules|evidence|support|build|cache|\.lake|\.venv|\.cache|primary|context|private|raw|search|extract|assets|html|pdf|images|receipts|bindings|downloads|artifacts|output|outputs|dist|target|\.git)([-_.]|$)',re.I)
ROLE=re.compile(r'brief|dispatch|role|tasks?|thread|transcript|prompt',re.I)
files=[];pruned=[]
for base in ['frontier','research','experiments','proposals','scouts','notes','findings','iterations']:
 start=ROOT/base
 if not start.is_dir():continue
 for d,dirs,names in os.walk(start,followlinks=False):
  for n in list(dirs):
   p=Path(d)/n
   if p.is_symlink() or ACTIVE.search(n) or DERIV.search(n) or ROLE.search(n):
    dirs.remove(n);pruned.append(str(p.relative_to(ROOT)))
  for n in names:
   p=Path(d)/n
   if p.is_symlink() or not p.is_file() or ACTIVE.search(n) or DERIV.search(n) or ROLE.search(n):continue
   if p.suffix.lower() in {'.pdf','.png','.jpg','.jpeg','.gif','.zip','.gz','.xz','.bz2','.tar','.mp4','.sqlite','.db','.woff','.woff2','.ttf','.otf','.olean','.so','.o','.a'}:continue
   files.append(str(p.relative_to(ROOT)))
(OUT/'private/search/rank-selected-paths.json').write_text(json.dumps(files,indent=2))
(OUT/'private/search/rank-pruning.json').write_text(json.dumps({'active':ACTIVE.pattern,'derivative':DERIV.pattern,'role':ROLE.pattern,'pruned':pruned},indent=2))
print('selected paths',len(files),'pruned',len(pruned),flush=True)
import subprocess
matches=[]
for i in range(0,len(files),200):
 r=subprocess.run(['rg','--hidden','--no-ignore','-l','-i',r'generali[sz]ed truncation|uniform matroid|corank.{0,30}profile|rank.{0,15}probe|liminf.{0,20}rank','--',*files[i:i+200]],cwd=ROOT,capture_output=True,timeout=20)
 if r.returncode not in (0,1):print('rg issue',r.returncode,r.stderr.decode()[:200],flush=True)
 matches.extend(r.stdout.decode().splitlines())
(OUT/'private/search/rank-matching-paths.json').write_text(json.dumps(matches,indent=2))
print('matching paths',len(matches),flush=True)
for p in matches:print(p)
