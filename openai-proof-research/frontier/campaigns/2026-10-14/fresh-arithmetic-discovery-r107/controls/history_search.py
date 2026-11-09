from pathlib import Path
import os,re,json,hashlib
ROOT=Path(__file__).resolve().parents[1]; PROJECT=ROOT.parents[3]
# Pruning applies to EACH component before descent or selection, including hidden names.
BLOCK=re.compile(r'(structural.*r143|analytic.*r136|analytic.*r137|t373e135-|analytic.*r135|k369r134-|t088p133-|review|release|publication|manuscript|render|vendor|fixture|inventory|corpus|copied|copies|copy|frozen|outside|control|intake|parent|evidence|inputs|ledger|source|upstream|node_modules|\.git|\.venv|__pycache__|formal|proof-r\d|contribution|private|context|search|extract|download|preprint|primary|scratch|work|assets|resources|catalogue|retriev|authentic|MANIFEST|tasks\.json|brief|receipt|register|checkpoint-copy)',re.I)
ACTIVE=re.compile(r'(?:arithmetic.*r(?:10[7-9]|1[1-9]\d|[2-9]\d\d)|structural.*r(?:13[6-9]|1[4-9]\d|[2-9]\d\d)|analytic.*r(?:13[5-9]|1[4-9]\d|[2-9]\d\d))',re.I)
HIT=re.compile(r'Egyptian|unit[ -]fraction|prescribed.denominator|short.fraction|totient|Erd[oőö]s.Graham|Vose|Bleicher|T025|I025|T024|I024',re.I)
starts=['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','iterations','experiments','proposals','scouts','notes','findings']
skip=[]; scanned=[]; hits=[]
for start in starts:
 base=PROJECT/start
 if not base.exists():continue
 for path,dirs,files in os.walk(base,topdown=True,followlinks=False):
  dirs[:]=sorted(d for d in dirs if not (BLOCK.search(d) or ACTIVE.search(d) or Path(path,d).is_symlink()))
  for name in sorted(files):
   if BLOCK.search(name) or ACTIVE.search(name):continue
   p=Path(path,name)
   if p.is_symlink():continue
   # No suffix, dotfile, ignore-file, or size filter. Binary detected after complete read.
   b=p.read_bytes()
   if b'\0' in b:continue
   try:t=b.decode('utf-8')
   except UnicodeDecodeError:continue
   rel=str(p.relative_to(PROJECT)); scanned.append(dict(path=rel,size=len(b),sha256=hashlib.sha256(b).hexdigest()))
   matches=[{'line':i,'text':s} for i,s in enumerate(t.splitlines(),1) if HIT.search(s)]
   if matches:hits.append({'path':rel,'matches':matches})
(ROOT/'private/history-search-refined.json').write_text(json.dumps({'roots':starts,'block':BLOCK.pattern,'active':ACTIVE.pattern,'queries':HIT.pattern,'scanned':scanned,'hits':hits},indent=2)+'\n')
print('Scanned',len(scanned),'authored text files; matching files',len(hits))
for h in hits:
 
 if any('egyptian' in m['text'].lower() or 'unit fraction' in m['text'].lower() for m in h['matches']):
  print(h['path'],len(h['matches']))
