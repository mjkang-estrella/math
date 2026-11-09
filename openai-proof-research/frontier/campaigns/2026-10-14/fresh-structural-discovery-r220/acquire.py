from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures,re
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r220');P=R/'private';pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
prefix='preprints/The-metric-Blaschke-theorem-September-23-2026'
t=json.loads(Path('sources/preprints-tree.json').read_bytes())['tree'];e=[x for x in t if x['path']==prefix or x['path'].startswith(prefix+'/')];assert len(e)==20
(P/'tree-selection.json').write_text(json.dumps(e,indent=2)+'\n')
def fetch(x):
 u=f'https://raw.githubusercontent.com/openai/math/{pin}/'+x['path'];b=urllib.request.urlopen(u,timeout=45).read();sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert sha==x['sha'] and len(b)==x['size']
 p=P/'canonical'/x['path'][len(prefix)+1:];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return dict(path=x['path'],local=p.relative_to(R).as_posix(),bytes=len(b),git_blob=sha,sha256=hashlib.sha256(b).hexdigest(),url=u,mode=x['mode'])
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:a=list(ex.map(fetch,[x for x in e if x['type']=='blob']))
assert len(a)==16
p='lean/docs/344.md';u=f'https://raw.githubusercontent.com/openai/math/{pin}/{p}';b=urllib.request.urlopen(u,timeout=45).read();m=json.load(urllib.request.urlopen(f'https://api.github.com/repos/openai/math/contents/{p}?ref={pin}',timeout=45));sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert sha==m['sha'];(P/'lean-344.md').write_bytes(b);a.append(dict(path=p,local='private/lean-344.md',bytes=len(b),git_blob=sha,sha256=hashlib.sha256(b).hexdigest(),url=u,mode='100644',authentication='pinned GitHub contents metadata'))
(P/'authentication.json').write_text(json.dumps(a,indent=2)+'\n')
print('Authenticated 16 canonical blobs and lean/docs/344.md')
for p in [P/'canonical/build/paper.tex',P/'lean-344.md',P/'canonical/README.md']:
 b=p.read_bytes();print('\nNAVIGATION',p.relative_to(R),len(b));
 for i,line in enumerate(b.splitlines(keepends=True),1):
  s=line.decode();
  if p.name=='paper.tex' and not re.search(r'\\(?:input|include|bibliography)|newcommand',s):continue
  print(str(i)+': '+s.rstrip())
# Boundary classification uses bytes.splitlines(keepends=True), never str.splitlines.
for p in sorted((P/'canonical/build/sections').iterdir()):
 off=0;print('\nBOUNDARIES',p.name)
 for i,l in enumerate(p.read_bytes().splitlines(keepends=True),1):
  s=l.decode()
  if re.search(r'acknow|acknol|thank|communicat|licen[cs]e|copyright|publisher',s,re.I):print(i,off,off+len(l),'MASKED EDITORIAL MARKER')
  elif re.search(r'\\(?:sub)*section|\\paragraph|\\begin\{(?:theorem|lemma|proposition|corollary|remark|definition)|\\input|\\include|\\cite',s):print(i,off,off+len(l),s.strip())
  off+=len(l)
 print('END',i,off)
