import pathlib,subprocess,re,json,hashlib
base=pathlib.Path.cwd(); own=pathlib.Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r124'); pkt=own/'packet'; out=pkt/'private/search';out.mkdir(exist_ok=True)
roots=[p for p in ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/scouts','proposals','experiments'] if pathlib.Path(p).is_dir()]
cmd=['rg','--files','--hidden','--no-ignore',*roots]; r=subprocess.run(cmd,capture_output=True)
excluded={'private','inputs','input','node_modules','.git','.venv','venv','__pycache__','snapshots','snapshot','controls','control-copies','final-controls','copied-controls','dependency','dependencies'}
files=[]
for b in r.stdout.splitlines():
 p=pathlib.Path(b.decode());
 if p.is_relative_to(own) or set(p.parts)&excluded or p.suffix.lower() not in {'.md','.tex','.txt','.json','.py'}:continue
 if not p.is_file() or p.is_symlink():continue
 files.append(p)
pat=r'(same.block.{0,50}(insert|relocat|reservoir)|(?:hard|exact).{0,35}(?:block.count|occupation|phase.restrict)|(?:canonical|fixed.count).{0,50}(?:Ruelle|moment|insert)|(?:228|149|263|084).{0,35}(?:count|kernel|routing|rate)|persistent.excitation|square.exponent|two.parameter.{0,25}(?:routing|ratio))'
rx=re.compile(pat,re.I); hits=[]; sizes=[]; removed=[]
for p in files:
 h=hashlib.sha256(); size=0; matches=[]
 with p.open('rb') as f:
  for n,line in enumerate(f,1):
   h.update(line);size+=len(line);s=line.decode('utf8','replace')
   if rx.search(s):matches.append({'line':n,'line_bytes':len(line),'line_sha256':hashlib.sha256(line).hexdigest(),'excerpt':s[:1000].rstrip()})
 sizes.append(size)
 if matches:hits.append({'path':str(p),'bytes':size,'sha256':h.hexdigest(),'matches':matches})
(out/'final-hits.json').write_text(json.dumps(hits,indent=2)+'\n')
rec={'argv':cmd,'exit':r.returncode,'stderr':r.stderr.decode(),'pattern':pat,'extensions':['md','tex','txt','json','py'],'excluded_components':sorted(excluded),'excluded_own':str(own),'no_size_cutoff':True,'work_scratch_included':True,'json_searched_as_text':True,'files':len(files),'bytes':sum(sizes),'largest':max(sizes),'matching_files':len(hits),'matching_lines':sum(len(x['matches']) for x in hits),'display_line_character_cap':1000,'inventory_sha256':hashlib.sha256(('\n'.join(map(str,files))+'\n').encode()).hexdigest(),'hits_local':'private/search/final-hits.json','hits_sha256':hashlib.sha256((out/'final-hits.json').read_bytes()).hexdigest()}
(pkt/'public/search-register.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps(rec,indent=2));print('\nMATCH PATHS\n'+'\n'.join(x['path'] for x in hits if not any(z in x['path'] for z in ['source-register','manifest','intake','FINAL','reading','receipt','identit','provenance'])))
