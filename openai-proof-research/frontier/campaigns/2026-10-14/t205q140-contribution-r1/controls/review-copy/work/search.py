import os,re,json,subprocess,hashlib,datetime,fnmatch
from pathlib import Path
base=Path.cwd(); own=base/'frontier/campaigns/2026-10-14/t205q140-contribution-r1'
# Pruning is before descent and filename enumeration. No size cutoff, no blanket private/work exclusion.
patterns=['k369r134-*','*arithmetic*r104*','*analytic*r134*','*arithmetic*r103*','t009p102-*','t088p133-*','discovery-analytic-r133-parent','t205q140-*']
corpus={'.git','node_modules','.venv','__pycache__','preprints','primary','rendered','controls','site-packages'}
files=[]; pruned=[]
for start in ['frontier','experiments','proposals','scouts','notes']:
 if not (base/start).is_dir():continue
 for root,dirs,names in os.walk(base/start,followlinks=False):
  keep=[]
  for d in dirs:
   if d in corpus or any(fnmatch.fnmatch(d.lower(),p) for p in patterns): pruned.append(str((Path(root)/d).relative_to(base)))
   elif (Path(root)/d).is_symlink():pruned.append(str((Path(root)/d).relative_to(base)))
   else:keep.append(d)
  dirs[:]=keep
  for f in names:
   p=Path(root)/f
   if any(any(fnmatch.fnmatch(c.lower(),q) for q in patterns) for c in p.relative_to(base).parts):continue
   if p.is_file() and not p.is_symlink():files.append(str(p.relative_to(base)))
query=r'Plancherel|fourth[ -]moment|tensor.{0,35}(mixing|chain)|staircase.{0,35}(mixing|asymptotic)|cycle[ -](index|profile)|T205Q|R026|R037'
hits=[]; errors=[]
for k in range(0,len(files),150):
 a=subprocess.run(['rg','--hidden','--no-ignore','--text','-l','-i','--',query,*files[k:k+150]],capture_output=True,text=True)
 if a.returncode not in (0,1):errors.append(a.stderr)
 hits.extend(a.stdout.splitlines())
(own/'packet/private/search-paths.txt').write_text('\n'.join(hits)+'\n')
# Bounded original-body previews; hash complete matching line, do not duplicate oversized encodings.
rx=re.compile(query,re.I); summaries=[]
for name in hits:
 matches=[]; total=0
 with open(base/name,'rb') as f:
  for ln,b in enumerate(f,1):
   s=b.decode('utf-8',errors='replace')
   if rx.search(s):
    total+=1
    if len(matches)<4:matches.append({'line':ln,'preview':s[:320].rstrip(),'bytes':len(b),'line_sha256':hashlib.sha256(b).hexdigest()})
 summaries.append({'path':name,'matching_lines':total,'first_matches':matches})
(own/'packet/private/search-hits.json').write_text(json.dumps(summaries,indent=2)+'\n')
(own/'packet/private/search-record.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'query':query,'case_insensitive':True,'text_includes_binary':True,'hidden_ignored':True,'no_filesize_cutoff':True,'component_patterns_pruned':patterns,'corpus_components_pruned':sorted(corpus),'pruned_paths':pruned,'files_searched':len(files),'files_hit':len(hits),'errors':errors,'scope':'Navigation only; no semantic-read/priority-clearance claim'},indent=2)+'\n')
print(json.dumps({'files_searched':len(files),'files_hit':len(hits),'errors':errors}))
