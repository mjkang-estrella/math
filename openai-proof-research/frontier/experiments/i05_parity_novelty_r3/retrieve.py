import json,re,hashlib,urllib.request,concurrent.futures,subprocess
from pathlib import Path
ROOT=Path.cwd(); OUT=ROOT/'frontier/sources/i05_parity_novelty_r3'; PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text()); entries={e['path']:e for e in tree['tree'] if e['type']=='blob'}
dirs=sorted({e['path'].split('/')[1] for e in tree['tree'] if e['type']=='tree' and e['path'].count('/')==1})
pattern='prime|parity|chowla|elliott|multiplicative|mobius|möbius|liouville|sieve|squarefree|dirichlet|shift|correlation|dickman|arithmetic-progression|hardy|mangoldt'
(OUT/'catalogue-screen.json').write_text(json.dumps({'pin':PIN,'truncated':tree['truncated'],'tree_entries':len(tree['tree']),'directory_count':len(dirs),'all_directories':dirs,'title_matches':[d for d in dirs if re.search(pattern,d,re.I)],'contents_matches':[{'line':i,'text':s} for i,s in enumerate((ROOT/'sources/CONTENTS.md').read_text().splitlines(),1) if re.search(pattern,s,re.I)]},indent=2))
jobs=[]
for p,e in entries.items():
 if not p.endswith('.tex'):continue
 isintro=p.endswith(('introduction.tex','01-introduction.tex','00-introduction.tex'))
 take=False
 if 'Ordinary-two-point-' in p:take=not '/build/main' in p
 if 'Prime-Predecessors-with-' in p:take=p.endswith(('main.tex','03-shifted.tex','05-type-ii.tex','07-extraction.tex'))
 if 'The-Poisson-Dirichlet-' in p:take=p.endswith(('01-introduction.tex','03-determinant.tex','06-correlations.tex','09-long-prime-appendix.tex'))
 if 'Weighted-Dilation-' in p:take=isintro or p.endswith(('02-transference.tex','04-shifted-correlations.tex'))
 if 'Primitive-roots-for-' in p:take=isintro or p.endswith('08-type-ii.tex')
 if 'Simultaneous-primitive-' in p:take=isintro or p.endswith('05-prime-reservoir.tex')
 if any(z in p for z in ['joint-Dickman','Squarefree-values','additive-indecomposability','Power-Saving-for-Polynomial']):take=isintro
 if take:jobs.append({'url':f'https://raw.githubusercontent.com/openai/math/{PIN}/{p}','file':'upstream/'+p,'pinned_path':p,'expected_git_blob':e['sha']})
for name,url in [
 ('carella-abs.html','https://arxiv.org/abs/2206.12956'),('carella-v3.pdf','https://arxiv.org/pdf/2206.12956v3'),('carella-v2.pdf','https://arxiv.org/pdf/2206.12956v2'),
 ('lichtman-abs.html','https://arxiv.org/abs/2009.08969'),('lichtman-v2.pdf','https://arxiv.org/pdf/2009.08969v2'),
 ('pintz-v1.pdf','https://arxiv.org/pdf/1004.1067v1'),('wang-abs.html','https://arxiv.org/abs/2609.14492'),('wang-v1.pdf','https://arxiv.org/pdf/2609.14492v1')]:jobs.append({'url':url,'file':name})
def run(j):
 r=dict(j)
 try:
  req=urllib.request.Request(j['url'],headers={'User-Agent':'Mozilla/5.0'})
  with urllib.request.urlopen(req,timeout=35) as f:b=f.read();r.update(status=f.status,final_url=f.url)
  path=OUT/j['file'];path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(b)
  r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if 'pinned_path'in j:
   r['git_blob']=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();r['pin_match']=r['git_blob']==j['expected_git_blob']
  if j['file'].endswith('.pdf'):
   z=subprocess.run(['pdftotext','-layout',str(path),str(path.with_suffix('.txt'))],capture_output=True);r['pdftotext_exit']=z.returncode
 except Exception as e:r['error']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:results=list(ex.map(run,jobs))
(OUT/'retrieval-manifest.json').write_text(json.dumps(results,indent=2))
print(json.dumps({'jobs':len(results),'ok':sum('sha256'in r for r in results),'failures':[r for r in results if 'error'in r],'pin_mismatches':[r for r in results if r.get('pin_match')==False]},indent=2))
