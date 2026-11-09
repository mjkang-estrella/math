from pathlib import Path
import os,re,json,hashlib
root=Path(__file__).resolve().parents[1]; repo=root.parents[3]
exclude={'private','inputs','input','dependencies','dependency','snapshots','snapshot','controls','control-copies','copied-controls','.git','node_modules','.lake','.venv','venv','__pycache__','vendor','upstream','primary','sources'}
pattern=r'mass[-– ]Hom|nonfree.{0,35}(quotient|support)|restriction[-: ]image|evaluation[- ]kernel|Foulkes|whole[- ]power|p[- ]permutation.{0,100}(rank|bound)|fixed[- ]total.{0,30}(order|grading)|Lipman|klt.{0,15}complement'
q=re.compile(pattern,re.I); files=[];errors=[];hits=[];total=0;mx=0
for anchor in ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','experiments','proposals','scouts']:
 for path,dirs,names in os.walk(repo/anchor):
  dirs[:]=[d for d in dirs if d not in exclude and not (Path(path)/d).is_relative_to(root) and not d.startswith('copied-controls')]
  for n in names:
   p=Path(path)/n
   if p.suffix.lower() not in {'.md','.tex','.txt','.json','.py'} or p.is_symlink():continue
   try:b=p.read_bytes()
   except OSError as e:errors.append([str(p),repr(e)]);continue
   total+=len(b);mx=max(mx,len(b));files.append(str(p.relative_to(repo)))
   for i,line in enumerate(b.decode(errors='replace').splitlines(),1):
    if q.search(line):hits.append({'path':str(p.relative_to(repo)),'line':i,'text':line})
out=root/'packet/private/search';(out/'final-hits.json').write_text(json.dumps(hits,ensure_ascii=False,indent=2)+'\n')
(out/'final-scope.json').write_text(json.dumps(dict(pattern=pattern,files=len(files),bytes=total,max_size=mx,excluded_components=sorted(exclude),own_excluded=True,hidden_ignored_included=True,size_cutoff=None,extensions=['md','tex','txt','json','py'],path_list_sha256=hashlib.sha256('\n'.join(sorted(files)).encode()).hexdigest(),hits=len(hits),errors=errors),indent=2)+'\n')
print(len(files),total,mx,len(hits),'errors',len(errors))
for x in hits:
 if x['path'].endswith('.md') and ('/packet/public/' in x['path'] or 'analytic-attempt.md' in x['path']) and not any(y in x['path'] for y in ['reading','REPORT','report.md','reproduction']):print(x['path'],x['line'],x['text'][:220])
