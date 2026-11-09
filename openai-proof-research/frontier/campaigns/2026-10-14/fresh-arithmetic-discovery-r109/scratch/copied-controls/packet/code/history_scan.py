from pathlib import Path
import os,re,json,hashlib,fnmatch
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
R=P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r109'
active=['h138-*','*h138-*','t185r144-*','*t185r144-*','*structural*r144*','*analytic*r138*','*arithmetic*r109*','*arithmetic*r108*','*arithmetic*r107*','*structural*r143*','t177c143-*','*analytic*r137*','*analytic*r136*','*analytic*r135*','t373e135-*','k369r134-*','t088p133-*']
roles=re.compile(r'(?:^|[^a-z])(?:proof\w*|readme|prepare|record.reads|contribution\w*|correctness\w*|proof.gate\w*|scratch\w*|work|family.titles|.*\.sha256|.*\.stat|inputs?\w*|private\w*|context\w*|external\w*|packet\w*|contents|preprints\w*|tree|digest\w*|bibliograph\w*|references|citations|review\w*|parent|intake\w*|brief\w*|dispatch\w*|role\w*|task\w*|cop(?:y|ies|ied)\w*|corpus\w*|inventor\w*|fixture\w*|control\w*|source\w*|primary\w*|literature\w*|search\w*|histor(?:y|ical)\w*|render\w*|vendor\w*|frozen\w*|outside\w*|formal\w*|manuscript\w*|release\w*|publication\w*|archive\w*|snapshot\w*|cache\w*|download\w*|extract\w*|metadata\w*|manifest\w*|receipt\w*|seal\w*|anchor\w*|catalog\w*|catalogue\w*|upstream\w*|raw|third.party|node.modules|\.git|venv|build\w*|dist|site.packages|expanded.target|prompt\w*|instruction\w*|handoff\w*|final|report|reading\w*|acquisition\w*|fetch\w*|verify\w*|authenticat\w*)(?:[^a-z]|$)')
query=re.compile(r'zero.generic|positive.characteristic.{0,80}(?:lex|EGH)|(?:lex|EGH).{0,80}positive.characteristic|p.central|commuting.form|wild.{0,30}division|Frobenius.{0,40}(?:EGH|powers)',re.I)
def blocked(s):
 s=s.lower()
 if any(fnmatch.fnmatch(s,a) for a in active):return 'explicit-round'
 # Coarse newer research-round exclusion, including flat derivative names.
 if re.search(r'(?:^|[^a-z])r(?:[1-9][0-9]{2,}|100)(?:[^0-9]|$)',s):return 'newer-round-coarse'
 if roles.search(s):return 'role-coarse'
 if s in {'.git','.venv','__pycache__'}:return 'binary/build'
 return None
roots=['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','iterations','experiments','proposals','scouts','notes','findings']
pruned=[]; hits=[]; scanned=0; omitted=[]
for root in roots:
 base=P/root
 if not base.is_dir():continue
 for d,dirs,files in os.walk(base,followlinks=False):
  keep=[]
  for n in dirs:
   why=blocked(n)
   if why:pruned.append([str((Path(d)/n).relative_to(P)),why])
   elif (Path(d)/n).is_symlink():pruned.append([str((Path(d)/n).relative_to(P)),'symlink'])
   else:keep.append(n)
  dirs[:]=keep
  for n in files:
   p=Path(d)/n; rel=str(p.relative_to(P)); why=blocked(n)
   if why:pruned.append([rel,why]);continue
   if p.is_symlink():omitted.append([rel,'symlink']);continue
   b=p.read_bytes()
   if b'\0' in b:omitted.append([rel,'NUL']);continue
   try:s=b.decode('utf-8')
   except UnicodeDecodeError:omitted.append([rel,'non-UTF8']);continue
   scanned+=1
   matches=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if query.search(l)]
   if matches:hits.append({'path':rel,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matches':matches})
result={'roots':roots,'scanned':scanned,'no_size_cutoff':True,'explicit_patterns':active,'pruned':pruned,'binary_omissions':omitted,'hits':hits,'limits':'Coarse filters can omit authored originals and admit disguised derivatives. Hits are navigation only. Newer >=100 rounds omitted; named completed originals require direct followup. No current-active-output or historical whole-project certificate.'}
(R/'private/search/history-aliases.json').write_text(json.dumps(result,indent=2)+'\n')
print('scanned',scanned,'pruned',len(pruned),'hits',len(hits))
for h in hits:
 print(h['path'])
 for m in h['matches'][:3]:print(' ',m['line'],m['text'][:400])
