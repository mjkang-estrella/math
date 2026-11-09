import pathlib,subprocess,re,json,hashlib
R=pathlib.Path('.');O=R/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r125'; roots=['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/scouts','proposals']
args=['rg','--files','--hidden','--no-ignore',*roots];p=subprocess.run(args,capture_output=True);assert p.returncode==0
excluded={'.git','.lake','node_modules','vendor','__pycache__','inputs','snapshots','frozen','upstream','primary','render','rendered','provenance','context'}
patterns=[r'\bThorp\b',r'conditional.coordinate.sweep',r'fault.{0,35}(sweep|line)',r'shrinking.{0,35}(slit|analytic)',r'analytic.{0,35}(perturb|sweep)',r'(biased|inhomogeneous).{0,50}(shuffle|sweep)',r'238',r'local.{0,25}(damage|defect).{0,25}(path|revea)']
rx=re.compile('|'.join(patterns),re.I); records=[]; errors=[]; count=0; total=0;hits=[]
for name in p.stdout.decode().splitlines():
 f=pathlib.Path(name)
 if O==f or O in f.parents or any(x in excluded for x in f.parts):continue
 if f.suffix.lower() not in {'.md','.txt','.json','.py','.tex','.lean','.html','.csv','.yaml','.yml','.rst','.sh'}:continue
 try:
  b=f.read_bytes();s=b.decode('utf-8');count+=1;total+=len(b)
 except Exception as e: errors.append({'path':name,'error':str(e)});continue
 rows=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if rx.search(l)]
 if rows:records.append({'path':name,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'hits':rows})
summary={'command':args,'roots':roots,'excluded_components':sorted(excluded),'extensions':'authored text/code/JSON; no size limit','patterns':patterns,'files_read':count,'bytes_read':total,'matched_files':len(records),'matched_lines':sum(len(x['hits']) for x in records),'errors':errors}
(O/'packet/private/search/history-summary.json').write_text(json.dumps(summary,indent=2)+'\n');(O/'packet/private/search/history-hits.json').write_text(json.dumps(records,indent=2)+'\n')
print(summary)
for x in records:
 if any(rx2 in x['path'] for rx2 in ['r113/','r122/','i13-']):continue
 if x['path'].endswith('.md') and any(re.search(r'biased|fault|perturb|slit',h['text'],re.I) and re.search(r'Thorp|sweep|slit',h['text'],re.I) for h in x['hits']):print(x['path'], [(h['line'],h['text'][:260]) for h in x['hits'] if re.search(r'biased|fault|perturb|slit',h['text'],re.I) and re.search(r'Thorp|sweep|slit',h['text'],re.I)])
