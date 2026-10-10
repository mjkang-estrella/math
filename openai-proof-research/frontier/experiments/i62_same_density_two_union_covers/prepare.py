from pathlib import Path
import hashlib,json,shutil,subprocess,re,requests,concurrent.futures
R=Path.cwd(); S=R/'frontier/sources/i62_same_density_two_union_covers'; E=R/'frontier/experiments/i62_same_density_two_union_covers'; C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'; old=R/'frontier/sources/i60_threshold_structural_combinatorics_discovery'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(p,v):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
mutable=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
paths=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json',*mutable,'frontier/iterations/i60-threshold-structural-combinatorics-discovery.md','frontier/experiments/i60-parent-verification.json']
paths += ['frontier/sources/i60_threshold_structural_combinatorics_discovery/'+p for p in ['full-brief.txt','objections.json','source-contracts.json','read-passages.json','seal.json','verification.json']]
for pattern in ['i13-*','i19-*','i22-*','i25-*']:
 paths += [str(p.relative_to(R)) for p in (R/'frontier/iterations').glob(pattern) if p.suffix=='.md']
inputs=[]
for path in paths:
 p=R/path;b=p.read_bytes();dest=S/'inputs'/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b);inputs.append(dict(path=path,frozen=str(dest.relative_to(R)),sha256=sha(b),mutable=path in mutable))
save(S/'inputs.json',inputs)
tree=json.loads((R/'sources/preprints-tree.json').read_text());lookup={x['path']:x for x in tree['tree'] if x['type']=='blob'}
assert len(tree['tree'])==13223 and len({x['path'].split('/')[1] for x in tree['tree']})==749
files=subprocess.check_output(['rg','--files','--no-ignore',str(C)],text=True).splitlines();inv=[];pins=[]
for name in sorted(files):
 p=Path(name);rel=str(p.relative_to(C));b=p.read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==lookup[rel]['sha'];inv.append(dict(path=rel,sha256=sha(b),git_blob=blob))
 if any(x in rel for x in ['Talagrands-discrete-convexity-conjecture-September-23-2026/','Integral-and-fractional-expectation-thresholds-are-equivalent-September-23-2026/']):
  dest=S/'pinned'/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b);pins.append(dict(path=rel,file=str(dest.relative_to(R)),sha256=sha(b),git_blob=blob,url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+rel))
save(S/'corpus-inventory.json',inv);save(S/'pinned-manifest.json',pins)
terms=['two.union','two.color','property.?B','critical core','discrete.convexity','selector','smallness']
cmd=['rg','--no-ignore','-n','-i','|'.join(terms),str(C)];r=subprocess.run(cmd,capture_output=True,text=True);save(S/'corpus-search.json',dict(command=cmd,returncode=r.returncode,lines=sorted(r.stdout.splitlines())))
hits=[]
for row in inputs:
 if '/iterations/i' not in row['path']:continue
 for i,line in enumerate((R/row['frozen']).read_text().splitlines(),1):
  for term in terms:
   if re.search(term,line,re.I):hits.append([row['path'],i,term,line])
save(S/'prior-search.json',dict(terms=terms,lines=sorted(hits)))
watch=[dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes())) for p in [old/'seal.json',old/'verification.json',R/'frontier/experiments/i60_threshold_structural_combinatorics_discovery/diagnostics.py',R/'frontier/experiments/i60_threshold_structural_combinatorics_discovery/verify.py']]
save(S/'old-watch.json',watch)
urls={
'li-abs':'https://arxiv.org/abs/2609.08967','li-pdf':'https://arxiv.org/pdf/2609.08967v2',
'park-abs':'https://arxiv.org/abs/2609.14681','park-pdf':'https://arxiv.org/pdf/2609.14681v1',
'ahpt-abs':'https://arxiv.org/abs/2608.11183','ahpt-pdf':'https://arxiv.org/pdf/2608.11183v1',
'fischer-person-abs':'https://arxiv.org/abs/2505.21782','fischer-person-pdf':'https://arxiv.org/pdf/2505.21782',
'lovasz-abs':'https://arxiv.org/abs/1903.04968','lovasz-pdf':'https://arxiv.org/pdf/1903.04968',
'fkp-pdf':'https://arxiv.org/pdf/2105.10905',
 'talagrand-2010':'https://michel.talagrand.net/preprints/small.pdf',
 'talagrand-2021-page':'https://michel.talagrand.net/upperandlower/index.html',
 'talagrand-2021-doi':'https://link.springer.com/book/10.1007/978-3-030-82595-9',
 'yang-abs':'https://arxiv.org/abs/2609.20864','yang-pdf':'https://arxiv.org/pdf/2609.20864v2'}
def fetch(item):
 name,url=item;row=dict(name=name,url=url)
 try:
  r=requests.get(url,timeout=35);row.update(status=r.status_code,final_url=r.url,content_type=r.headers.get('content-type'));ext='.pdf' if r.content.startswith(b'%PDF') else '.html';p=S/'literature'/(name+ext);p.parent.mkdir(exist_ok=True);p.write_bytes(r.content);row.update(file=str(p.relative_to(R)),sha256=sha(r.content))
  if ext=='.pdf':
   dest=p.with_suffix('.txt');rr=subprocess.run(['pdftotext','-layout',str(p),str(dest)],capture_output=True);row['conversion_status']=rr.returncode
   if dest.exists():row.update(text=str(dest.relative_to(R)),text_sha256=sha(dest.read_bytes()))
 except Exception as exc:row['error']=str(exc)
 return row
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:responses=list(ex.map(fetch,urls.items()))
save(S/'literature/responses.json',responses)
print(json.dumps(dict(inputs=len(inputs),corpus=len(inv),pins=len(pins),search_hits=len(r.stdout.splitlines()),primary=[{k:x[k] for k in ['name','status','error'] if k in x} for x in responses]),indent=2))
