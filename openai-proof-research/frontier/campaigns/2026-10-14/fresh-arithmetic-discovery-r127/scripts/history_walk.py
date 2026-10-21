from pathlib import Path
import os,fnmatch,json,re,hashlib
root=Path.cwd(); own=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r127'); pol=json.loads((own/'isolation-policy.json').read_text())
q=re.compile(r'cyclic.quotient|Noether.normali[sz]ation|parameter.ideal|embedding.dimension|Hilbert.Samuel|Fano[ -]type|Cartier.{0,30}(section|divisor)|discriminant.{0,12}(divisor|b.divisor)|log.canonical.threshold|Birkar|Shokurov|minimal.log.discrepanc|normalized.volume',re.I)
def denied(p):
 s=p.as_posix().lower()
 return s.startswith(str(own).lower()) or any(fnmatch.fnmatch(s,g) for g in pol['round_globs']) or any(x in s for x in pol['coarse_substrings']+pol['explicit_substrings'])
hits=[];errors=[];pruned=[];n=0;largest=0
for base,dirs,files in os.walk(root,topdown=True,followlinks=False):
 rel=Path(base).relative_to(root)
 keep=[]
 for d in dirs:
  p=rel/d
  if (rel==Path('.') and d not in pol['roots']) or denied(p) or (root/p).is_symlink():pruned.append(str(p))
  else: keep.append(d)
 dirs[:]=keep
 for f in files:
  p=rel/f
  if rel==Path('.') or denied(p) or (root/p).is_symlink():pruned.append(str(p));continue
  try: raw=(root/p).read_bytes();s=raw.decode('utf-8')
  except (OSError,UnicodeError) as e:errors.append({'path':str(p),'error':str(e)});continue
  n+=1;largest=max(largest,len(raw))
  matches=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if q.search(l)]
  if matches:hits.append({'path':str(p),'size':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'matches':matches})
out={'files_decoded':n,'largest':largest,'hits':hits,'pruned':pruned,'errors':errors}
(own/'private/history-screen.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'files_decoded':n,'largest':largest,'pruned':len(pruned),'errors':len(errors),'matches':len(hits)}))
for h in hits:print(h['path'],','.join(str(x['line']) for x in h['matches']))
