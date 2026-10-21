from pathlib import Path
import os,re,json,hashlib,urllib.request,concurrent.futures
ROOT=Path(__file__).resolve().parent
PROJECT=ROOT.parents[3]
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b):return hashlib.sha256(b).hexdigest()
def download_sources(family='083'):
 tpath=PROJECT/'sources/preprints-tree.json'; raw=tpath.read_bytes(); tree=json.loads(raw)
 assert len(tree['tree'])==13223 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 (ROOT/'private/preprints-tree.json').write_bytes(raw)
 prefix={'083':'preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/','363':'preprints/Nonuniqueness-with-local-conservation-for-the-hard-sphere-Boltzmann-equation-October-5-2026/','363old':'preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/','225':'preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/'}[family]
 entries=[x for x in tree['tree'] if x['type']=='blob' and x['path'].startswith(prefix) and x['path'].endswith(('.tex','.bib','.md'))]
 def get(x):
  url=f"https://raw.githubusercontent.com/openai/math/{PIN}/{x['path']}"
  b=urllib.request.urlopen(url,timeout=50).read(); blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert len(b)==x['size'] and blob==x['sha']
  dest=ROOT/'private/upstream'/x['path']; dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
  return dict(path=x['path'],url=url,size=len(b),gitblob=blob,sha256=sha(b),local=str(dest.relative_to(ROOT)),read_extent='acquired; not yet recorded as read')
 with concurrent.futures.ThreadPoolExecutor(max_workers=4) as e: ledger=list(e.map(get,entries))
 old=json.loads((ROOT/'source-ledger.json').read_text()) if (ROOT/'source-ledger.json').exists() else []
 ledger={x['path']:x for x in old+ledger}
 (ROOT/'source-ledger.json').write_text(json.dumps(list(ledger.values()),indent=2)+'\n')
 print('Acquired authenticated source files',len(ledger))
def scan(family='083'):
 # Pruned at each directory and file before opening. No Git ignore and no size cap.
 mandatory=re.compile(r'^t177c143-|structural.*r14[34]|arithmetic.*r10[78]|t373e135|analytic.*r135|k369r134|t088p133',re.I)
 roles=re.compile(r'(^|[-_.])(private|primary|literature|history|search|index|evidence|source[s]?|input[s]?|context|snapshot[s]?|frozen|cop(y|ies|ied)|corpus|inventor\w*|fixture[s]?|control[s]?|vendor|render\w*|build|dist|cache|packet|recovery|followup|handoff|parent|intake|review\w*|release|publication|manuscript|formal|\.lake|node_modules|\.git|work|scratch|download\w*|extract\w*|catalog\w*|metadata|receipt[s]?|pinned|manifest|seal|verif\w*|prompt[s]?|brief[s]?|task[s]?|instruction[s]?|pause|checkpoint|outside)([-_.]|$)',re.I)
 needles=re.compile(r'Hilbert.{0,100}(Lipschitz|vector field|direction)|Lipschitz.{0,100}(Hilbert|direction)|Stein.{0,40}(vector|weak.?type)|Source0?83\b|\b[TIK]0?83[A-Z]|directional.{0,30}(variation|sparse|truncat)|\bBateman\b|\bLacey.?Li\b',re.I)
 if family=='225': needles=re.compile(r'six.?vertex|\b225\b|multiplicative.chaos|electric.vertex|chiral.gaussian|arcsin.c',re.I)
 pruned=[]; admitted=[]; hits=[]; omitted=[]
 bases=['frontier/campaigns/2026-10-14','frontier/iterations','frontier/experiments','frontier/scouts','frontier/findings','proposals','notes','research']
 for base in bases:
  start=PROJECT/base
  if not start.exists():continue
  for cur,dirs,files in os.walk(start,topdown=True,followlinks=False):
   q=Path(cur)
   keep=[]
   for n in sorted(dirs):
    p=q/n; why=None
    if p==ROOT:why='current-root'
    elif mandatory.search(n):why='explicit-exclusion'
    elif roles.search(n):why='role-pruning'
    elif p.is_symlink():why='symlink'
    elif (m:=re.search(r'(?:^|[-_])r(\d+)(?:[-_]|$)',n,re.I)) and int(m[1])>=125:why='coarse-recent-round'
    elif q==start and base.startswith('frontier/campaigns') and not re.fullmatch(r'fresh-(analytic|arithmetic|structural|operator|algebra)-discovery-r\d+',n):why='coarse-generic-campaign-activity-unknown'
    if why:pruned.append([str(p.relative_to(PROJECT)),why])
    else:keep.append(n)
   dirs[:]=keep
   for n in sorted(files):
    p=q/n; rel=str(p.relative_to(PROJECT))
    if mandatory.search(n) or roles.search(n):pruned.append([rel,'file-role-or-explicit']);continue
    if p.is_symlink() or not p.is_file():continue
    b=p.read_bytes()
    if b'\0' in b:omitted.append([rel,'binary-NUL']);continue
    try:s=b.decode('utf-8')
    except UnicodeDecodeError:omitted.append([rel,'non-UTF8']);continue
    admitted.append(dict(path=rel,size=len(b),sha256=sha(b)))
    ls=[dict(line=i,text=l) for i,l in enumerate(s.splitlines(),1) if needles.search(l)]
    if ls:hits.append(dict(path=rel,hits=ls))
 result=dict(bases=bases,mandatory=mandatory.pattern,roles=roles.pattern,needle=needles.pattern,pruned=pruned,omitted=omitted,admitted=admitted,hits=hits)
 (ROOT/('private/history-search-'+family+'.json')).write_text(json.dumps(result,indent=2)+'\n')
 print('History files searched',len(admitted),'hit files',len(hits),'pruned',len(pruned))
 for x in hits:print(x['path'],[(z['line'],z['text'][:220]) for z in x['hits'][:5]])
if __name__=='__main__':
 import sys
 {'sources':download_sources,'scan':scan}[sys.argv[1]](sys.argv[2] if len(sys.argv)>2 else '083')
