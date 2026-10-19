from pathlib import Path
import os,re,json,hashlib,time
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); OWN=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r93'; OUT=OWN/'packet/private/search'
patterns={
 'bloch':r'(?i)(?:source\s*0?40\b|T040|Bloch.{0,30}(?:surface|conjecture)|torsion (?:order|motive)|decomposition of (?:the )?diagonal|universal.{0,25}CH.?0)',
 'hikita':r'(?i)(?:Hikita|source\s*0?44\b|T044|Coulomb.{0,30}(?:fixed|cohomology))',
 'pixton':r'(?i)(?:Pixton|source\s*0?53\b|T053|tautological.{0,20}(?:relation|ideal))',
 'contact':r'(?i)(?:LeBrun|source\s*0?62\b|T062|contact.{0,20}(?:Fano|classification))',
 'mcm':r'(?i)(?:source\s*195\b|T195|small.{0,12}Cohen|MCM.{0,30}(?:rank|domain))',
 'quillen':r'(?i)(?:source\s*310\b|T310|Quillen.{0,25}(?:homology|conjecture))',
 'anti':r'(?i)(?:source\s*0?68\b|T068|anticanonical.{0,30}(?:index|indices|invariant))'}
rx={k:re.compile(v) for k,v in patterns.items()}; ex={'.git','.lake','node_modules','vendor','dependencies','private','inputs','context','snapshots','snapshot','frozen','upstream','primary','preprints','corpus','control-work','controls-work','copies','copy','__pycache__','output','dist','build'}; ext={'.md','.txt','.tex','.json','.jsonl','.py','.lean','.log','.yaml','.yml','.csv','.tsv','.bib','.rst','.sh'}
files=0;total=0;hits={k:0 for k in rx}; errors=[];inv=hashlib.sha256(); handles={k:(OUT/(k+'.jsonl')).open('w') for k in rx}
for base in ['frontier','experiments','proposals','findings','notes','reviews','tmp']:
 for d,dirs,names in os.walk(ROOT/base,followlinks=False):
  dirs[:]=[n for n in dirs if n not in ex and not (Path(d)/n).is_symlink() and Path(d)/n!=OWN]
  for n in names:
   p=Path(d)/n
   if p.suffix.lower() not in ext or p.is_symlink():continue
   try:b=p.read_bytes();s=b.decode('utf8',errors='replace')
   except Exception as e:errors.append([str(p),str(e)]);continue
   files+=1;total+=len(b);rel=str(p.relative_to(ROOT));sha=hashlib.sha256(b).hexdigest();inv.update((rel+'\0'+sha+'\n').encode())
   for k,r in rx.items():
    if not r.search(s):continue
    for i,line in enumerate(s.splitlines(),1):
     if r.search(line):handles[k].write(json.dumps({'path':rel,'sha256':sha,'line':i,'text':line[:1800]},ensure_ascii=False)+'\n');hits[k]+=1
for h in handles.values():h.close()
r={'patterns':patterns,'roots':['frontier','experiments','proposals','findings','notes','reviews','tmp'],'excluded_directory_names':sorted(ex),'extensions':sorted(ext),'no_input_size_cutoff':True,'files':files,'bytes':total,'hits':hits,'errors':errors,'inventory_digest':inv.hexdigest(),'inventory_retained':False,'display_line_cap':1800}
(OUT/'method.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
