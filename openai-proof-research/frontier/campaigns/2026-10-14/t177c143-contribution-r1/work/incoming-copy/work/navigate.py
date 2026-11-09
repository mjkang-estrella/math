from pathlib import Path
import os,re,json,subprocess,sys
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
O=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r143'
# Applied to directory AND file components before traversal or selection.
def banned(s):
 s=s.lower()
 return (s.startswith(('t373e135-','k369r134-','t088p133-')) or ('analytic' in s and any(r in s for r in ['r135','r136','r137'])) or ('arithmetic' in s and 'r107' in s)
  or any(t in s for t in ['review','intake','parent','corpus','fixture','control','venv','frozen','outside','render','inventory','snapshot','preserv','manifest','receipt','brief','task','primary','original','vendor','download','extract','capture','search','history','provenance','catalog','recovery','contribution','proof-r','pinned','preprints','output','ledger','routing','formal','.lake','mathlib','fetched','literature','scratch','family-map','family-titles','family-mention','families.txt','upstream','source','copy','copied','mirror','release','publication','manuscript','node_modules','.git'])
  or s in ['work','README.md','private','inputs','input','evidence','archives','archive','cache','__pycache__','build','dist','fresh-structural-discovery-r143']
  or ('r14' in s and not any(x in s for x in ['r140','r141','r142'])))
roots=['campaigns','iterations','experiments','proposals','scouts','notes','findings']
keep=[];omit=[]
for r in roots:
 start=P/'frontier'/r
 if not start.exists(): continue
 for d,ds,fs in os.walk(start,topdown=True,followlinks=False):
  good=[]
  for s in ds:
   q=Path(d)/s
   if banned(s) or q.is_symlink(): omit.append(str(q.relative_to(P)))
   else: good.append(s)
  ds[:]=good
  for s in fs:
   q=Path(d)/s
   if banned(s) or q.is_symlink() or q.suffix.lower() in ['.pdf','.png','.jpg','.zip','.gz','.tar','.pyc','.woff','.mp4','.olean']: continue
   keep.append(str(q))
pattern=sys.argv[1]
hits=[]
for i in range(0,len(keep),100):
 p=subprocess.run(['rg','--hidden','--no-ignore','-n','-i','-e',pattern,'--',*keep[i:i+100]],capture_output=True,text=True)
 if p.returncode not in [0,1]: raise RuntimeError(p.stderr)
 hits.extend(p.stdout.splitlines())
(O/'packet/private/navigation-coherent.json').write_text(json.dumps({'pattern':pattern,'files':len(keep),'pruned':omit,'policy':Path(__file__).read_text()},indent=2))
(O/'packet/private/history-hits-coherent.txt').write_text('\n'.join(hits)+'\n')
print('files',len(keep),'hits',len(hits),'pruned roots',len(omit))
print('\n'.join(sorted(set(x.split(':',1)[0] for x in hits))))
