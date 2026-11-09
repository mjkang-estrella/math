from pathlib import Path
import os,re,json,hashlib,datetime,subprocess,urllib.request,concurrent.futures
ROOT=Path(__file__).resolve().parents[1]; PROJECT=ROOT.parents[3]
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b): return hashlib.sha256(b).hexdigest()
def excluded(n):
 return (n=='.git' or n=='fresh-arithmetic-discovery-r104' or n.startswith('t088p133-') or n=='discovery-analytic-r133-parent' or re.search(r'(?:structural.*r140|analytic.*r134)',n) is not None or re.search(r'(?:^|-)(review|proof|contribution|formal|manuscript|release)(?:-|$)',n) is not None)
def search(tag,pattern,supplement=False):
 corpus={'.git','node_modules','.venv','__pycache__','downloads','raw','preprints','render','renders','build','target','dist','search'}
 if not supplement: corpus.update({'inputs','snapshots','frozen','private','work','sources','payload','context'})
 else: corpus.update({'inputs','snapshots','frozen','payload','context'})
 files=[];pruned=[]
 for start in ['frontier','experiments','proposals','scouts','notes','findings']:
  p=PROJECT/start
  if not p.exists():continue
  for d,ds,fs in os.walk(p,followlinks=False):
   for n in list(ds):
    if excluded(n) or n in corpus or (Path(d)/n).is_symlink(): ds.remove(n);pruned.append(str((Path(d)/n).relative_to(PROJECT)))
   for n in fs:
    p=Path(d)/n
    if p.is_symlink() or n=='tree.json' or n in {'preprints-tree.json','CONTENTS.md'}:continue
    files.append(str(p.relative_to(PROJECT)))
 out=ROOT/'packet/private/search'/tag;out.mkdir(exist_ok=True)
 hits=[]
 for i in range(0,len(files),250):
  r=subprocess.run(['rg','--hidden','--no-ignore','-l','-i','-e',pattern,'--',*files[i:i+250]],cwd=PROJECT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  if r.returncode not in [0,1]:raise RuntimeError(r.stderr.decode())
  hits.extend(r.stdout.decode().splitlines())
 (out/'files.txt').write_text('\n'.join(files)+'\n');(out/'hits.txt').write_text('\n'.join(hits)+'\n')
 (out/'scope.json').write_text(json.dumps({'utc':now(),'pattern':pattern,'supplement':supplement,'prune_components':sorted(corpus),'additional_pruning':'all active named roots/parents at every depth; t088p133-*; discovery-analytic-r133-parent; review/proof/contribution/formal/manuscript/release directory tokens; symlinks','files':len(files),'hits':len(hits),'size_cutoff':None,'binary_policy':'rg default detection','pruned':pruned},indent=2)+'\n')
 print(tag,len(files),len(hits));print('\n'.join(hits[:100]))
def acquire():
 tree=json.loads((PROJECT/'sources/preprints-tree.json').read_text())['tree']; selected=[x for x in tree if x['type']=='blob' and x['path'].endswith(('.tex','.bib','.md')) and any(z in x['path'] for z in ['Fiber-functors-for-finite-symmetric','Integral-Counterexample-to-Gersten','Integral-Degree-Three-Gersten'])]
 def one(x):
  url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path'];b=urllib.request.urlopen(url,timeout=45).read();g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(); assert len(b)==x['size'] and g==x['sha'];p=ROOT/'packet/private/sources'/x['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return {'path':x['path'],'url':url,'size':len(b),'git_blob':g,'sha256':sha(b),'acquired_utc':now(),'read':'not yet recorded'}
 with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: receipts=list(pool.map(one,selected))
 (ROOT/'packet/private/sources/acquisition.json').write_text(json.dumps(receipts,indent=2)+'\n');print('authenticated',len(receipts),'pinned blobs')
if __name__=='__main__':
 import sys
 if sys.argv[1]=='acquire':acquire()
 else: search(sys.argv[1],r'Gersten|Verlinde|Benson.{0,3}Etingof|higher.symmetric.tensor|ramified.regular.local',len(sys.argv)>2)
