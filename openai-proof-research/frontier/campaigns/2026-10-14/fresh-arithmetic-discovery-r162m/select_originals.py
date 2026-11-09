from pathlib import Path
import os,fnmatch,re,json,hashlib
ROOT=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162m')
p=json.loads((ROOT/'packet/private/EXCLUSIONS.json').read_text())
def blocked(path):
 s=path.as_posix().casefold()
 return any(fnmatch.fnmatchcase(s,g) for g in p['wildcards']) or any(g in s for g in p['substrings']) or any(fnmatch.fnmatchcase(c,g) for c in s.split('/') for g in p['extra_basename_wildcards'])
pat=re.compile(r'fourier.{0,20}restrict|restriction.{0,20}(?:ellipt|curv|sphere)|elliptic.{0,12}capacit|wave[ -]?packet|furstenberg|schr[oö]|near[ -]?extrem|bourgain|positive(?:ly)?.{0,12}curv',re.I)
hits=[]; stats=dict(decoded=0,non_utf8=0,pruned=0,symlinks=0)
for top in ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings']:
 if blocked(Path(top)) or not Path(top).is_dir(): continue
 for base,dirs,files in os.walk(top,followlinks=False):
  keep=[]
  for n in sorted(dirs):
   q=Path(base)/n
   if blocked(q):stats['pruned']+=1
   elif q.is_symlink():stats['symlinks']+=1
   else:keep.append(n)
  dirs[:]=keep
  for n in sorted(files):
   q=Path(base)/n
   if blocked(q):stats['pruned']+=1;continue
   if q.is_symlink():stats['symlinks']+=1;continue
   b=q.read_bytes()
   try:s=b.decode('utf-8')
   except UnicodeDecodeError:stats['non_utf8']+=1;continue
   stats['decoded']+=1
   ms=list(pat.finditer(s))
   if ms:
    hits.append(dict(path=q.as_posix(),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),matches=[dict(start=len(s[:m.start()].encode()),end=len(s[:m.end()].encode()),text=m.group()) for m in ms]))
(ROOT/'packet/private/original-selection.json').write_text(json.dumps(dict(stats=stats,hits=hits),indent=2)+'\n')
print(stats)
for h in hits:print(h['path'],h['bytes'],len(h['matches']),sorted(set(m['text'] for m in h['matches']))[:10])
