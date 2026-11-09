from pathlib import Path
import os,fnmatch,json,re,hashlib
base=Path('.'); out=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162/packet/private'); p=json.loads((out/'guard-policy.json').read_text())
def reject(path):
 s=path.as_posix().casefold()
 return any(x in s for x in p['substrings']) or any(fnmatch.fnmatchcase(s,x) for x in p['wildcards'])
alias=re.compile(r'ehresmann|stratified.{0,35}(isotop|trivial|transport)|controlled.{0,25}vector.field|conical.{0,25}(singular|trivial)|h.cobord|finite.{0,20}base.change|angular.seam|gradient.lift|sectional.milnor|wahl.{0,25}invariant',re.I)
allowed={'campaigns','iterations','experiments','proposals','scouts','notes','findings'}
hits=[]; read=bad=0
for dp,ds,fs in os.walk(base,topdown=True,followlinks=False):
 d=Path(dp); ds[:]=[n for n in ds if not (d/n).is_symlink() and not reject(d/n)]
 for n in fs:
  q=d/n
  if reject(q) or q.is_symlink() or not any(x.casefold() in allowed for x in q.parts): continue
  b=q.read_bytes()
  try: s=b.decode('utf-8')
  except UnicodeDecodeError: bad+=1; continue
  read+=1; matches=list(alias.finditer(s))
  if matches:
   snippets=[{'char':m.start(),'text':s[max(0,m.start()-100):min(len(s),m.end()+140)]} for m in matches[:6]]
   hits.append(dict(path=q.as_posix(),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),count=len(matches),snippets=snippets))
(out/'expanded-navigation.json').write_text(json.dumps({'utf8_candidates':read,'non_utf8':bad,'hits':hits},indent=2)+'\n')
print('Candidates',read,'nonUTF8',bad,'hit paths',len(hits))
for h in hits: print(h['path'],h['bytes'],h['count'],repr(h['snippets'][0]['text'][:240]))
