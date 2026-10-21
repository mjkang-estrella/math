from pathlib import Path
import os,json,fnmatch,re
ROOT=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r151')
p=json.loads((ROOT/'private/ISOLATION-POLICY.json').read_text())
patterns=p['broad_full_path_casefold']+['*history[0-9]*','*screen*','*diagnostic*','*proof-r*','*summary*']
roots=['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','iterations','experiments','proposals','scouts','notes','findings']
rx=re.compile(r'(hilbert.{0,90}(?:lipschitz|direction|vector.field)|(?:lipschitz|direction|vector.field).{0,90}hilbert|stein.{0,35}(?:weak|conjecture)|phase.prediction|popular.forest)',re.I)
result={'patterns':patterns,'roots':roots,'missing_roots':[],'pruned':[],'decoded':[],'binary':[],'errors':[],'symlinks':[],'hits':[]}
def denied(s):return any(fnmatch.fnmatchcase(s.lower(),p) for p in patterns)
for base in roots:
 if not Path(base).exists():result['missing_roots'].append(base);continue
 if denied(base):result['pruned'].append(base);continue
 for dp,ds,fs in os.walk(base,topdown=True,followlinks=False):
  keep=[]
  for d in ds:
   q=Path(dp)/d;s=q.as_posix()
   if q.is_symlink():result['symlinks'].append(s)
   elif denied(s):result['pruned'].append(s)
   else:keep.append(d)
  ds[:]=keep
  for f in fs:
   q=Path(dp)/f;s=q.as_posix()
   if q.is_symlink():result['symlinks'].append(s);continue
   if denied(s) or q.suffix.lower() in {'.py','.js','.sh','.ts','.tsx','.mjs','.cjs','.ipynb'}:result['pruned'].append(s);continue
   try:
    b=q.read_bytes()
    if b'\0' in b:result['binary'].append(s);continue
    text=b.decode('utf8');result['decoded'].append(s)
   except (OSError,UnicodeError) as e:result['errors'].append([s,str(e)]);continue
   hits=[{'line':i+1,'text':line} for i,line in enumerate(text.splitlines()) if rx.search(line)]
   if hits:result['hits'].append({'path':s,'matches':hits})
(ROOT/'private/history-scan.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:len(v) for k,v in result.items() if k not in {'patterns','roots'}})
for h in result['hits']:
 print(h['path'],len(h['matches']))
 for m in h['matches'][:2]:print(m['line'],m['text'][:500])
