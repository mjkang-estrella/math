from pathlib import Path
import os,fnmatch,json,subprocess,hashlib
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN=ROOT/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r144'
peer=['*structural*r149*','*arithmetic*r113*','*structural*r150*','*arithmetic*r114*']
hist=['*analytic*r143*','*analytic*r142*','*analytic*r141*','*analytic*r140*','*analytic*r139*','*structural*r148*','*structural*r147*','*structural*r146*','*structural*r145*','*arithmetic*r112*','*arithmetic*r111*','*arithmetic*r110*','*arithmetic*r109*','*arithmetic*r108*','*arithmetic*r107*','*analytic*r138*','*structural*r144*','*structural*r143*','*analytic*r137*','*analytic*r136*','*analytic*r135*','*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
derivative=['corpus','source','primary','history-derivative','search','inventory','fixture','control','extract','render','vendor','build','copy','copied','frozen','role','formal','manuscript','release','parent','private','input','upstream','shortlist','context','fetched','scratch','preprint','catalogue','receipt','brief','intake','bundle','recovery','literature','history','venv','site-packages','packet','payload','work','archive','snapshot','cache','dist-info','download','external','third-party']
patterns=peer+hist+['*'+s+'*' for s in derivative]+['.git','node_modules','fresh-analytic-discovery-r144']
def excluded(n): return any(fnmatch.fnmatchcase(n.lower(),p) for p in patterns)
# No ancestor search; pruning occurs before any descent or content selection.
counts={'pruned_components':0,'symlinks':0,'binary_nonutf8':0,'utf8':0}; admitted=[]
for base,ds,fs in os.walk(ROOT,topdown=True,followlinks=False):
 keep=[]
 for n in ds:
  p=Path(base)/n
  if excluded(n): counts['pruned_components']+=1
  elif p.is_symlink(): counts['symlinks']+=1
  else: keep.append(n)
 ds[:]=keep
 for n in fs:
  p=Path(base)/n
  if excluded(n): counts['pruned_components']+=1; continue
  if p.is_symlink(): counts['symlinks']+=1; continue
  b=p.read_bytes()
  try: s=b.decode('utf8')
  except UnicodeDecodeError: counts['binary_nonutf8']+=1; continue
  if '\0' in s: counts['binary_nonutf8']+=1; continue
  counts['utf8']+=1; admitted.append(str(p))
# rg sees only preselected UTF8 files, including hidden, ignored, JSON and large files.
pat=r'(?i)(allen.?cahn|de.?giorgi|source0?375|i375|t375|finite.morse|sheet.pack|stable.bernstein|energy.growth)'
hits=[]
for k in range(0,len(admitted),150):
 p=subprocess.run(['rg','--hidden','--no-ignore','-n','--with-filename',pat,*admitted[k:k+150]],capture_output=True,text=True)
 if p.returncode not in (0,1): raise RuntimeError(p.stderr)
 hits.append(p.stdout)
(OWN/'private/history-hits-v2.txt').write_text(''.join(hits))
(OWN/'private/history-scan-v2.json').write_text(json.dumps({'root':str(ROOT),'patterns':patterns,'counts':counts,'admitted_files':admitted},indent=2)+'\n')
print(json.dumps(counts)); print('hit lines',sum(x.count('\n') for x in hits))
