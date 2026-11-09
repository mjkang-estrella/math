from pathlib import Path
import os,json,subprocess,re
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
R=P/'frontier/campaigns/2026-10-14/t177c143-proof-r1'
def excluded(s):
 s=s.lower()
 if any(x in s for x in ['t177c143','t373e135','k369r134','t088p133']):return True
 if 'analytic' in s and any(x in s for x in ['r135','r136','r137']):return True
 if 'arithmetic' in s and 'r107' in s:return True
 if 'structural' in s and 'r144' in s:return True
 if s=='fresh-structural-discovery-r143':return True
 return any(x in s for x in ['review','contribution','proof-r','parent','intake','brief','task','copy','copied','corpus','fixture','control','source','primary','private','input','evidence','frozen','outside','archive','render','vendor','venv','node_modules','.git','.lake','mathlib','snapshot','preserv','inventory','download','extract','build','cache','manifest','receipt','provenance','ledger','navigation','history','catalog','recovery','context','followup','fetched','literature','pinned','preprints','release','publication','manuscript','formal','output','baseline','authentication','mutation']) or s in ['work','scratch','dist','__pycache__']
keep=[];pruned=[];rejected=[];missing=[]
for root in ['campaigns','iterations','experiments','proposals','scouts','notes','findings']:
 start=P/'frontier'/root
 if not start.is_dir():missing.append(str(start.relative_to(P)));continue
 for d,ds,fs in os.walk(start,topdown=True,followlinks=False):
  good=[]
  for s in ds:
   p=Path(d)/s
   if excluded(s) or p.is_symlink():pruned.append(str(p.relative_to(P)))
   else:good.append(s)
  ds[:]=good
  for s in fs:
   p=Path(d)/s
   if excluded(s) or p.is_symlink() or p.suffix.lower() in ['.pdf','.png','.jpg','.jpeg','.zip','.gz','.tar','.pyc','.woff','.mp4','.olean','.so']:
    rejected.append(str(p.relative_to(P)));continue
   keep.append(str(p))
pattern=r'coboundary|cofill|Khot|Anantharam|shared.?random|grand.?coupl|tree.?gauge|family.?177|source.?177|cut.?equivari|Walsh|coherent.{0,30}fill'
hits=[]
for i in range(0,len(keep),80):
 p=subprocess.run(['rg','--hidden','--no-ignore','-n','-i','-e',pattern,'--',*keep[i:i+80]],capture_output=True,text=True,timeout=25)
 assert p.returncode in (0,1),p.stderr
 hits.extend(p.stdout.splitlines())
out=R/'packet/private/search';out.mkdir(parents=True,exist_ok=True)
for name in ['hits.txt','navigation.json']:
 p=out/name
 if p.exists():p.rename(out/('first-pass-'+name))
(out/'hits.txt').write_text('\n'.join(hits)+'\n')
(out/'navigation.json').write_text(json.dumps({'pattern':pattern,'policy':'Top-down pruning on every directory and filename; hidden/ignored/JSON/large text included with no size cutoff. Symlinks not followed. Coarse filters omit authored material. Counts/hits are navigation only.','selected':keep,'pruned':pruned,'rejected':rejected,'missing_roots':missing,'hits':len(hits)},indent=2)+'\n')
paths=sorted(set(x.split(':',1)[0] for x in hits))
print(json.dumps({'selected_files':len(keep),'hits':len(hits),'hit_files':len(paths),'pruned_directories':len(pruned),'missing':missing},indent=2))
print('\n'.join(paths[:100]))
