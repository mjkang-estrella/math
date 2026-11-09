from pathlib import Path
import os,fnmatch,subprocess,json,hashlib
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r142'
patterns=['t373e135-*','*analytic*r135*','*arithmetic*r106*','k369r134-*','t088p133-*','*review*','*contribution*','*proof-r*','*parent*','*intake*','*release*','*manuscript*','*publication*','*formal*','*brief*','*inventory*','*snapshot*','*copied*','*control*','*fixture*','*search*','*render*','*corpus*','*source*','*upstream*','*frozen*','*outside*','*baseline*','*tree.json','*catalog*','*preprints__*','*preprints--*','*history*','*manifest*','*acquisition*','*receipt*','*authentication*','*pinned-blob*','*external-input*','*family-map*','*family-path*','*selection*','*hits*','*correctness*','*gate*','*proof*','*retrieval*','*fetch-log*','*families*','*family-title*','*alias-path*','*bindings*','*-task.json']
exact={'.git','.venv','venv','node_modules','inputs','input','recovery-context','context','downloads','download','primary','primaries','intro','scan','history','provenance','external','build','output','dist','cache','__pycache__','fresh-structural-discovery-r142'}
source_names={x['path'].split('/')[1].lower() for x in json.loads((P/'sources/preprints-tree.json').read_text())['tree'] if x['path'].startswith('preprints/')}
def bad(n): return n.lower() in source_names or n.lower() in exact or any(fnmatch.fnmatch(n.lower(),q) for q in patterns)
files=[]
for top in ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings']:
 base=P/top
 if not base.is_dir():continue
 for here,ds,fs in os.walk(base,followlinks=False):
  ds[:]=[d for d in ds if not bad(d) and not (Path(here)/d).is_symlink()]
  for n in fs:
   p=Path(here)/n
   if bad(n) or p.is_symlink():continue
   if p.suffix.lower() in {'.pdf','.png','.jpg','.zip','.gz','.xz','.mp4','.woff','.ttf','.pyc','.olean'}:continue
   files.append(str(p.relative_to(P)))
(R/'packet/private/navigation-files.json').write_text(json.dumps(files,indent=2))
query=r'(lex|Betti|Koszul|ideal|monomial).{0,65}(flag|subquotient|nested|interval quotient|relative simplicial)|(flag|subquotient|nested|interval quotient|relative simplicial).{0,65}(lex|Betti|Koszul|ideal|monomial)|Duval|distraction'
results=[]
for i in range(0,len(files),300):
 p=subprocess.run(['rg','-n','-i','--text',query,'--',*files[i:i+300]],cwd=P,text=True,capture_output=True)
 if p.returncode not in (0,1):raise RuntimeError(p.stderr)
 results.append(p.stdout)
out=''.join(results); (R/'packet/private/navigation-hits.txt').write_text(out)
(R/'packet/private/navigation-policy.json').write_text(json.dumps({'patterns':patterns,'exact':sorted(exact),'files':len(files),'hit_lines':len(out.splitlines()),'size_cutoff':None,'hidden_and_ignored':True},indent=2))
print('searched',len(files),'hit lines',len(out.splitlines()))
counts={}
for l in out.splitlines():
 f=l.split(':',1)[0]; counts[f]=counts.get(f,0)+1
print('\n'.join(f'{v} {k}' for k,v in sorted(counts.items(),key=lambda kv:-kv[1])[:65]))
