from pathlib import Path
import os,fnmatch,json,re,hashlib
root=Path('.'); own=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r155'); dest=own/'packet/private'; policy=json.loads((dest/'isolation-policy.json').read_text())
def denied(p):
 s=p.as_posix().casefold()
 return any(x in s for x in policy['substrings']) or any(fnmatch.fnmatchcase(s,w) for w in policy['wildcards'])
scopes={'campaigns','iterations','experiments','proposals','scouts','notes','findings'}
terms=re.compile(r'minimal[ -]model|flip[ -]termination|termination of.{0,30}flip|difficulty|shokurov|mori.{0,8}fib|b[ -]divisor|generalized.{0,8}pair|k[aä]hler|log[ -]canonical|q[ -]factorial|nonvanishing|abundance|boundedness|terminal singular',re.I)
results=[]; count=bad=0
for d,dirs,files in os.walk(root,followlinks=False):
 dp=Path(d); dirs[:]=[x for x in dirs if not (dp/x).is_symlink() and not denied(dp/x)]
 if not scopes.intersection(dp.parts): continue
 for n in files:
  p=dp/n
  if p.is_symlink() or denied(p): continue
  b=p.read_bytes()
  try: s=b.decode('utf-8')
  except UnicodeDecodeError: bad+=1; continue
  count+=1
  matches=[{'start':m.start(),'term':m.group(),'context':s[max(0,m.start()-100):min(len(s),m.end()+180)]} for m in terms.finditer(s)]
  if matches: results.append({'path':p.as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matches':matches})
(dest/'history-navigation.json').write_text(json.dumps({'eligible_utf8':count,'non_utf8':bad,'hits':results},indent=2)+'\n')
print('Eligible UTF8',count,'nonUTF8',bad,'hit files',len(results))
for r in results:
 print(r['path'],len(r['matches'])); print('\n'.join(m['context'].replace('\n',' ') for m in r['matches'][:3]))
