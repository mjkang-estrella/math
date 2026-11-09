from pathlib import Path
import os,fnmatch,json,re,hashlib,time
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r220');g=json.loads((R/'guards.json').read_bytes())
def denied(p):
 s=p.as_posix().casefold()
 return any(x in s for x in g['substrings']) or any(fnmatch.fnmatchcase(s,x) for x in g['wildcards']+g['derivatives']) or s==R.as_posix().casefold() or s.startswith(R.as_posix().casefold()+'/')
# Construction aliases derived from all ten operative sections. No bare geometry nouns.
q=re.compile(r'(?:metric[ -]+blaschke|blaschke[ -]+(?:rigidity|conjecture|cut[ -]?locus|geodesic[ -]?space)|injectivity[ -]+radius.{0,45}(?:equals|equal to|diameter)|compact[ -]+rank[ -]+one[ -]+symmetric.{0,30}classification|weighted[ -]+lagrangian[ -]+comparison|(?:berger[ -]+kazdan|kazdan.{0,25}(?:scalar|weighted|inequality))|(?:schur[ -]+complement.{0,40}(?:cut[ -]?pair|jacobi|half[ -]?period))|(?:cut[ -]?incidence.{0,40}pontryagin)|(?:first[ -]+free[ -]?loop[ -]+attachment)|(?:blaschke.{0,50}volume[ -]+algebra))',re.I)
admin=re.compile(r'status|provenance|scope.and.evidence|contribution.screen|acceptance|handoff|disposition|audit|reading|source|bibliograph|reference|coordination|campaign|intake|summary|limitations|navigation',re.I)
counts=dict(directories=0,pruned_directories=0,eligible_files=0,utf8_files=0,decode_failures=0,symlinks=0,matched_files=0,seconds=0);hits=[];start=time.monotonic()
for root,dirs,files in __import__('itertools').chain.from_iterable(os.walk(root,followlinks=False) for root in ['proposals','findings','experiments','notes']):
 rp=Path(root);counts['directories']+=1
 good=[]
 for d in dirs:
  p=rp/d
  if p.is_symlink():counts['symlinks']+=1;continue
  if denied(p):counts['pruned_directories']+=1;continue
  good.append(d)
 dirs[:]=good
 for f in files:
  p=rp/f
  if denied(p):continue
  if p.is_symlink():counts['symlinks']+=1;continue
  counts['eligible_files']+=1;b=p.read_bytes()
  try:s=b.decode('utf-8')
  except UnicodeDecodeError:counts['decode_failures']+=1;continue
  counts['utf8_files']+=1
  if not q.search(s):continue
  counts['matched_files']+=1;lines=b.splitlines(keepends=True);off=0;headings=[];matches=[]
  for i,l in enumerate(lines,1):
   st=l.decode();hm=re.match(r'^(#{1,6})\s+(.*)',st) or re.match(r'^\\((?:sub)*section)\*?\{(.*)',st)
   if hm:headings.append(dict(line=i,byte=off,heading=hm.group(2).strip(),level=len(hm.group(1)) if hm.group(1).startswith('#') else hm.group(1).count('sub')+1))
   if q.search(st):matches.append((i,off))
   off+=len(l)
  for i,o in matches:
   prev=[h for h in headings if h['line']<=i];h=prev[-1] if prev else dict(line=1,byte=0,heading='[unstructured; needs manual classification]',level=0)
   nxt=next((hh for hh in headings if hh['line']>h['line'] and hh['level']<=h['level']),dict(line=len(lines)+1,byte=len(b)))
   record=dict(path=p.as_posix(),file_sha256=hashlib.sha256(b).hexdigest(),match_line=i,heading=h,stop=nxt,administrative=bool(admin.search(h['heading'])))
   hits.append(record)
counts['seconds']=round(time.monotonic()-start,3)
(R/'private/history-navigation-other.json').write_text(json.dumps(dict(counts=counts,hits=hits,limits='Full relative path guards are prospective, coarse and nonexhaustive; no peer status read; broad own-root excluded. No size, dotfile, ignored-file, JSON or TeX cutoff. Content matches are navigation, not proof reads.'),indent=2)+'\n')
print(json.dumps(counts));
seen=set()
for h in hits:
 key=(h['path'],h['heading']['line'])
 if key in seen:continue
 seen.add(key);print(json.dumps({k:h[k] for k in ['path','heading','stop','administrative']}))
