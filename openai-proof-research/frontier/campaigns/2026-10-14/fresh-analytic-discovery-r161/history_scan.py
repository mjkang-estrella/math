import os,pathlib,re,json,hashlib
from isolation import excluded,ROOT,synthetic_test
synthetic_test()
pat=re.compile(r'(?i)(?<![\w])(?:cartan[\s–—-]*hadamard|cat\s*\(?\s*0\s*\)?\s*spaces?|sharp.{0,25}fillings?|isoperimetr\w*|integral\s+(?:cycles?|currents?)|filling\s+radius|filling\s+volume)(?![\w])')
read=[]; hits=[]; skipped=[]; prunes={'dirs':0,'files':0,'symlinks':0};errors=[]
def walk(d):
 for ent in sorted(os.scandir(d),key=lambda e:e.name):
  p=pathlib.Path(ent.path); rel=p.relative_to('.') if str(p).startswith('./') else p
  if ent.is_symlink():prunes['symlinks']+=1;continue
  if excluded(rel):prunes['dirs' if ent.is_dir(follow_symlinks=False) else 'files']+=1;continue
  if ent.is_dir(follow_symlinks=False):walk(p);continue
  if not ent.is_file(follow_symlinks=False):continue
  try:b=p.read_bytes()
  except OSError as e:errors.append([str(p),str(e)]);continue
  try:s=b.decode('utf-8')
  except UnicodeDecodeError:skipped.append(str(p));continue
  read.append({'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
  lines=[i for i,line in enumerate(s.splitlines(),1) if pat.search(line)]
  if lines:hits.append({'path':str(p),'lines':lines})
walk(pathlib.Path('.'))
(ROOT/'private/history/scan-membership.json').write_text(json.dumps({'decoded':read,'nonutf8':skipped,'prunes':prunes,'errors':errors,'hits':hits},indent=2)+'\n')
print(json.dumps({'decoded_count':len(read),'nonutf8':len(skipped),'prunes':prunes,'errors':errors,'hits':hits},indent=2))
