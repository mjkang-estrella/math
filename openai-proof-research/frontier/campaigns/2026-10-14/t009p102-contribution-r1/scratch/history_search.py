import os, pathlib, subprocess, gzip, json, hashlib
BASE = pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN = BASE/'frontier/campaigns/2026-10-14/t009p102-contribution-r1'
roots = ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/scouts','frontier/findings','proposals','notes','findings']
excluded_names = {'fresh-structural-discovery-r138','t088p133-manuscript-review-r1','t009p102-contribution-r1','.git','node_modules','__pycache__','preprints','author-copy','copied-author','inputs','outside','review-controls'}
pattern = r'Milnor|Steinberg|Bogomolov|Izhboldin|infinitesimal.{0,40}rigid|toral.{0,30}deriv|p.curvature|logarithmic.{0,30}deriv|mod.p\^n'
files=[]; skipped=[]; missing=[]
for root in roots:
    path=BASE/root
    if not path.exists(): missing.append(root); continue
    for cur, dirs, names in os.walk(path,followlinks=False):
        good=[]
        for d in sorted(dirs):
            if d in excluded_names or ('t088' in d.lower() and 'manuscript' in d.lower()) or pathlib.Path(cur,d).is_symlink():
                skipped.append(str(pathlib.Path(cur,d).relative_to(BASE)))
            else: good.append(d)
        dirs[:]=good
        for f in sorted(names):
            p=pathlib.Path(cur,f)
            if p.is_file() and not p.is_symlink(): files.append(str(p.relative_to(BASE)))
dest=OWN/'private/history-search';dest.mkdir(exist_ok=True)
metadata={'roots':roots,'missing':missing,'excluded_directory_names':sorted(excluded_names),'additional_exclusion':'any directory whose name contains both t088 and manuscript; directory symlinks','skipped':skipped,'pattern':pattern,'files':len(files),'size_cutoff':None,'hidden_ignored_json_binary':'included, rg -a --hidden --no-ignore','limits':'Copied corpus outside/inputs/preprints excluded; arbitrary authored work inside these names can be missed. No absence certificate.'}
(dest/'files.json').write_text(json.dumps(files,indent=2)+'\n')
raw=bytearray(); errors=bytearray()
for i in range(0,len(files),200):
    q=subprocess.run(['rg','-a','-n','-i','--hidden','--no-ignore','--',pattern,*files[i:i+200]],cwd=BASE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    raw.extend(q.stdout);errors.extend(q.stderr)
metadata.update({'raw_bytes':len(raw),'raw_sha256':hashlib.sha256(raw).hexdigest(),'stderr_bytes':len(errors)})
with gzip.open(dest/'matches.txt.gz','wb') as f:f.write(raw)
(dest/'stderr.txt').write_bytes(errors)
(dest/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
print(json.dumps({k:v for k,v in metadata.items() if k!='skipped'}))
hits={}
for line in raw.splitlines():
    name=line.split(b':',1)[0].decode('utf8','replace');hits[name]=hits.get(name,0)+1
(dest/'hit-files.json').write_text(json.dumps(hits,indent=2)+'\n')
print('Matching files',len(hits))
