from pathlib import Path
import os,re,json,hashlib,urllib.request,concurrent.futures
ROOT=Path(__file__).resolve().parent
PROJECT=ROOT.parents[3]
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def digest(b):return hashlib.sha256(b).hexdigest()
def fetch_source():
 tree=json.loads((PROJECT/'sources/preprints-tree.json').read_text())['tree']
 rows=[x for x in tree if x['type']=='blob' and 'A-finite-time-singularity-of-Calabi-flow-on-projective-space-' in x['path'] and x['path'].endswith(('.tex','.bib','.md'))]
 def one(x):
  url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path']; b=urllib.request.urlopen(url,timeout=45).read()
  g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert g==x['sha'] and len(b)==x['size']
  dest=ROOT/'private/source'/x['path'];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
  return dict(canonical_path=x['path'],url=url,size=len(b),git_blob=g,sha256=digest(b),local_path=str(dest.relative_to(ROOT)))
 with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:out=list(ex.map(one,rows))
 (ROOT/'source-ledger.json').write_text(json.dumps(out,indent=2)+'\n')
 print('Authenticated source files:',len(out))
def history():
 excluded=[];admitted=[];hits=[]
 # Coarse role pruning deliberately sacrifices some old author work to avoid active/copy trees.
 pat=re.compile(r'(?i)(structural.*r143|arithmetic.*r107|t373e135|analytic.*r135|k369r134|t088p133|(?:^|[-_])(recovery|followup|context|packet|work|search|catalogue|catalog|metadata|ledger|manifest|private|evidence|artifacts|out|output|archive|cache|raw|primary|frozen|review|proof-review|contribution|parent|intake|release|publication|manuscript|render|vendor|corpus|inventory|fixture|frozen|snapshot|inputs|copies|copy|control|sources?|downloads?|extract|build|\.git|node_modules|\.venv)(?:$|[-_])|(?:^|[-_])r(?:12[5-9]|1[3-9][0-9]|[2-9][0-9]{2})(?:$|[-_])|active)')
 alias=re.compile(r'(?i)(harmonic.{0,40}(growth|dimension)|361|tangent.cone|polynomial.growth|frequency.pinching)')
 for start in ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','experiments','proposals','notes']:
  base=PROJECT/start
  if not base.exists():continue
  for dp,dns,fns in os.walk(base,topdown=True,followlinks=False):
   kept=[]
   for d in dns:
    q=Path(dp)/d
    if pat.search(d) or q.is_symlink() or q==ROOT:excluded.append(str(q.relative_to(PROJECT)))
    else:kept.append(d)
   dns[:]=kept
   for f in fns:
    q=Path(dp)/f;rel=str(q.relative_to(PROJECT))
    if pat.search(f) or q.is_symlink():excluded.append(rel);continue
    # All filename extensions/hidden files admitted; binary bodies not searched.
    b=q.read_bytes()
    if b'\0' in b:continue
    try:s=b.decode('utf-8')
    except UnicodeDecodeError:continue
    admitted.append(dict(path=rel,size=len(b),sha256=digest(b)))
    matches=[dict(line=i,text=line) for i,line in enumerate(s.splitlines(),1) if alias.search(line)]
    if matches:hits.append(dict(path=rel,matches=matches))
 (ROOT/'private/history/search.json').write_text(json.dumps(dict(aliases=alias.pattern,pruning_regex=pat.pattern,excluded=excluded,admitted=admitted,hits=hits),indent=2)+'\n')
 print('History text bodies searched:',len(admitted),'pruned paths:',len(excluded),'hit files:',len(hits))
 for h in hits:
  substantive=[m for m in h['matches'] if re.search(r'(?i)calabi|abreu|U\(10\)|biharmonic',m['text'])]
  if False: print(h['path'])
if __name__=='__main__':
 import sys
 {'source':fetch_source,'history':history}[sys.argv[1]]()
