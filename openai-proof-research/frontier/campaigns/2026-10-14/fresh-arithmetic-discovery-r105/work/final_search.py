import os,re,json,hashlib,datetime
from pathlib import Path
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');R=P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r105'
D=R/'packet/private/search'
# Directory components are rejected before descent. File components get the same test.
blocked=re.compile(r'structural.*r141|analytic.*r135|^k369r134-|^discovery-analytic-r134-parent$|^fresh-analytic-discovery-r134$|^t088p133-|^discovery-analytic-r133-parent$|^fresh-arithmetic-discovery-r105$|(?:^|[-_])(review|reviews|proof|contribution|manuscript|release|formal)(?:[-_]|$)',re.I)
corpus={'search','history','recovery-context','copied','copies','originals','intake','snapshot','snapshots','node_modules','venv','.venv','.git','__pycache__','raw','preprints','downloads','download','primary','literature','corpus','corpora','context','inputs','input','fixtures','controls','control','frozen','outside','renders','render','site-packages','build','dist','target','extracted','sources','frontier-sources'}
pat=re.compile(r'finitistic|selection.process|Heisenberg|Hankel|Schr[oö]|extinction|central.character|linear.complexity',re.I)
files=[];hits=[];pruned=[];fail=[]
for rootname in ['frontier','iterations','experiments','proposals','scouts','notes','findings']:
 root=P/rootname
 if not root.exists():continue
 for base,dirs,names in os.walk(root,followlinks=False):
  keep=[]
  for n in dirs:
   p=Path(base)/n
   if blocked.search(n) or n.lower() in corpus or re.search(r'control|fixture|copied|corpus|upstream|source|fetch|download|outside|frozen|context|snapshot|extract|render|archive|replay',n,re.I) or p.is_symlink():pruned.append(str(p.relative_to(P)))
   else:keep.append(n)
  dirs[:]=keep
  for n in names:
   p=Path(base)/n
   if p.suffix.lower() in {'.tex','.bib','.html','.pdf','.png','.jpg','.zip','.tar','.gz'} or blocked.search(n) or p.is_symlink() or re.search(r'brief|catalogue|inventory|receipt|manifest|binding|acquisition|hits|search|corpus|history-|history_|file[-_]?(list|domain)|preprints-tree|source-register|canonical-selection|family-map|families|family-titles',n,re.I):continue
   # No filesize or extension cutoff; includes dotfiles, ignored files and JSON.
   try:
    b=p.read_bytes()
    if b'\0' in b:continue
    s=b.decode('utf-8')
   except (OSError,UnicodeError) as e:fail.append([str(p.relative_to(P)),str(e)]);continue
   rel=str(p.relative_to(P)); files.append(rel)
   matches=[(i,l[:1500]) for i,l in enumerate(s.splitlines(),1) if pat.search(l)]
   if matches:hits.append(dict(path=rel,sha256=hashlib.sha256(b).hexdigest(),matches=matches))
(D/'final-scope.json').write_text(json.dumps(dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),blocked=blocked.pattern,corpus=sorted(corpus),pattern=pat.pattern,files=files,pruned=pruned,failures=fail),indent=2)+'\n')
(D/'final-hits.json').write_text(json.dumps(hits,indent=2)+'\n')
print('searched',len(files),'text files; matched',len(hits),'files; decode/read failures',len(fail))
for h in hits:
 if any(re.search('finitistic|extinction',l,re.I) for i,l in h['matches']):
  print(h['path'])
  for i,l in h['matches'][:2]:print(i,l[:450])
