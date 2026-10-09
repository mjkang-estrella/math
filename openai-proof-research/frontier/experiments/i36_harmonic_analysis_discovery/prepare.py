from pathlib import Path
import hashlib,json,re,shutil,datetime,concurrent.futures,urllib.request,urllib.error,subprocess
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i36_harmonic_analysis_discovery'
CACHE=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
sha=lambda b:hashlib.sha256(b).hexdigest()
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text())
blobs={r['path']:r for r in tree['tree'] if r['type']=='blob'}
manifest=json.loads((CACHE.parent/'corpus-manifest.json').read_text())
cm={r['path']:r for r in manifest['files']}
names=['The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026','The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026','Almost-everywhere-Fourier-convergence-in-L-log-L-September-23-2026']
rows=[]
for name in names:
 for p in sorted((CACHE/'preprints'/name).rglob('*')):
  if not p.is_file():continue
  rel=str(p.relative_to(CACHE));b=p.read_bytes();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert git==blobs[rel]['sha']==cm[rel]['git_blob'] and sha(b)==cm[rel]['sha256']
  dest=OUT/'pinned'/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
  rows.append(dict(path=rel,local=str(dest.relative_to(ROOT)),sha256=sha(b),git_blob=git,bytes=len(b),url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{rel}'))
(OUT/'pinned-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
queries=[r'Erd.{0,12}s similarity',r'geometric.{0,30}(progression|sequence)',r'simultaneous.{0,100}ratio',r'Carleson',r'Fourier.{0,40}convergence',r'quasipolynomial',r'positively.curved.{0,30}surface']
audit=[];files=sorted(p for p in CACHE.rglob('*') if p.is_file())
for q in queries:
 hits=[]
 for p in files:
  t=p.read_text(errors='replace')
  found=[{'line':i,'text':l[:500]} for i,l in enumerate(t.splitlines(),1) if re.search(q,l,re.I)]
  if found:hits.append({'path':str(p.relative_to(CACHE)),'hits':found})
 audit.append({'query':q,'files_scanned':len(files),'hits':hits})
(OUT/'corpus-search-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
prior=[]
for p in sorted((ROOT/'frontier').glob('*/*.md')):
 if p.name.startswith('i36'):continue
 lines=p.read_text().splitlines();hits=[{'line':i,'text':s} for i,s in enumerate(lines,1) if re.search(r'Fourier|Carleson|geometric.progression|Erd.{0,10}s similarity|Kakeya|avoiding.set',s,re.I)]
 if hits:prior.append({'path':str(p.relative_to(ROOT)),'sha256':sha(p.read_bytes()),'hits':hits})
(OUT/'prior-search-audit.json').write_text(json.dumps(prior,indent=2)+'\n')
lit=OUT/'literature';lit.mkdir(exist_ok=True)
urls={
 'adjacent-current':'https://arxiv.org/abs/2610.11449',
 'adjacent-v1':'https://arxiv.org/html/2610.11449v1',
 'progressions-current':'https://arxiv.org/abs/2210.09284',
 'progressions-v1':'https://arxiv.org/pdf/2210.09284v1',
 'chlebik-current':'https://arxiv.org/abs/1512.05607',
 'chlebik-v1':'https://arxiv.org/pdf/1512.05607v1',
 'twofold-current':'https://arxiv.org/abs/2607.03584',
 'twofold-v2':'https://arxiv.org/html/2607.03584v2',
 'rajchman-current':'https://arxiv.org/abs/2609.04456',
 'rajchman-v1':'https://arxiv.org/html/2609.04456v1',
 'variation-primary':'https://webhomes.maths.ed.ac.uk/~wright/papers/osttw0710.pdf',
 'carleson-current':'https://arxiv.org/abs/2204.08051',
 'kolountzakis-primary':'https://arxiv.org/pdf/math/9603218',
}
def get(item):
 name,url=item;rec={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-provenance/1.0'}),timeout=45) as resp:
   b=resp.read();rec.update(status=resp.status,final_url=resp.url,headers=dict(resp.headers))
 except urllib.error.HTTPError as e:b=e.read();rec.update(status=e.code,error=str(e))
 except Exception as e:rec.update(error=repr(e));return rec
 ext='.pdf' if b.startswith(b'%PDF') else '.html';dest=lit/(name+ext);dest.write_bytes(b)
 rec.update(path=str(dest.relative_to(ROOT)),sha256=sha(b),bytes=len(b))
 if ext=='.pdf':
  txt=dest.with_suffix('.txt');run=subprocess.run(['pdftotext','-layout',str(dest),str(txt)],capture_output=True)
  rec['pdftotext_status']=run.returncode
  if txt.exists():rec['text_path']=str(txt.relative_to(ROOT));rec['text_sha256']=sha(txt.read_bytes())
 else:
  from html.parser import HTMLParser
  class Text(HTMLParser):
   def __init__(self):super().__init__();self.parts=[]
   def handle_data(self,data):self.parts.append(data)
  parser=Text();parser.feed(b.decode('utf-8',errors='replace'))
  txt=dest.with_suffix('.txt');txt.write_text('\n'.join(parser.parts));rec['text_path']=str(txt.relative_to(ROOT));rec['text_sha256']=sha(txt.read_bytes())
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:results=list(pool.map(get,urls.items()))
(lit/'manifest.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps({'pinned_files':len(rows),'corpus_files_scanned':len(files),'retrievals':[{k:r.get(k) for k in ('name','status','bytes','error')} for r in results]},indent=2))
