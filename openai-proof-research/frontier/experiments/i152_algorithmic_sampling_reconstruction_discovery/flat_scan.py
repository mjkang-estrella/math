"""One flat pinned-corpus and prior-report scan; no ancestor execution."""
from pathlib import Path
import hashlib,json,re,time
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i152_algorithmic_sampling_reconstruction_discovery'
assert not (S/'seal.json').exists()
def load(p):return json.loads((R/p).read_text())
def save(n,x):(S/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
old=load('frontier/sources/i148_polynomial_index_torus_subpackets/inheritance.json')
lex=[load(p) for p in old['lexical_records']]+[load('frontier/sources/i148_polynomial_index_torus_subpackets/lexical-search.json')]
patterns={k:v for a in lex for k,v in a['patterns'].items()}
new={'algorithmic_sampling_reconstruction':r'(?i)(contingency|cell.bounded|trace.reconstruction|log.concave.sampl|approximate.oracle|first.order.oracle|noisy.gradient|heterogeneous.channel|weighted.sampl)'}
patterns.update(new);rx={k:re.compile(v) for k,v in patterns.items()};computed={k:[] for k in patterns}
domain=load('frontier/sources/i112_inverse_boundary_discovery/search-domain.json')
tree=load('frontier/sources/i112_inverse_boundary_discovery/snapshots/sources/preprints-tree.json')['tree'];blobs={x['path']:x for x in tree if x['type']=='blob'}
assert len(tree)==13223 and len(blobs)==len(domain)==10373
assert sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree)==749
bindings=[];start=time.time()
for x in domain:
 b=(R/x['local']).read_bytes();o=b if x['local']==x['original_local'] else (R/x['original_local']).read_bytes()
 assert sha(b)==x['sha256'] and sha(o)==x['original_sha256']
 assert hashlib.sha1(b'blob '+str(len(o)).encode()+b'\0'+o).hexdigest()==x['git_sha']==blobs[x['path']]['sha']
 bindings.append({'path':x['path'],'text_sha256':sha(b),'original_sha256':sha(o),'kind':x['kind']})
 for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
  for k,pat in rx.items():
   ms=list(pat.finditer(line))
   if ms:computed[k].append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(m.span()) for m in ms]))
for a in lex:
 for k,v in a['results'].items():assert computed[k]==v,k
assert sum(x['kind']=='outside_pdf' for x in domain)==776
save('lexical-search.json',{'patterns':new,'results':{k:computed[k] for k in new},'scope':'Exact ordered matching-line multisets and zero-based codepoint positions after UTF-8 replacement decode and splitlines; lexical coverage is not semantic reading.'})
save('flat-traversal.json',dict(status='PASS',tree_entries=len(tree),manuscripts=749,original_blob_positions=len(domain),pdf_text_bindings=776,bindings=bindings,lexical_counts={k:len(v) for k,v in computed.items()},elapsed_seconds=time.time()-start,scope='One flat traversal; no corpus copy, PDF extraction, ancestor verifier or diagnostic execution.'))
paths=set(load('frontier/sources/i145_arithmetic_automorphic_discovery/overlap-search.json')['paths'])
paths.update(str(p.relative_to(R)) for p in (R/'frontier/iterations').glob('*.md'))
paths={p for p in paths if not re.search(r'/(?:i|iteration)(150|151|152)[-_]',p)}
paths.discard('frontier/iterations/README.md')
expr=r'(?i)(contingency|cell.bounded|weighted.switch|trace.reconstruction|log.concave.sampl|approximate.oracle|first.order.oracle|entropy.round|family (115|122|139))'
pat=re.compile(expr);results=[];refs=[]
for p in sorted(paths):
 b=(R/p).read_bytes();refs.append(dict(path=p,sha256=sha(b)))
 for i,line in enumerate(b.decode().splitlines(),1):
  ms=list(pat.finditer(line))
  if ms:results.append(dict(path=p,splitlines_line=i,text=line,spans=[list(m.span()) for m in ms]))
save('overlap-search.json',dict(expression=expr,paths=sorted(paths),refs=refs,results=results,scope='Frozen full prior-report domain; no active I150/I151 dependencies; family numbers are not iteration numbers.'))
print(json.dumps({'status':'PASS','corpus':len(domain),'new_lexical_lines':len(computed['algorithmic_sampling_reconstruction']),'overlap_reports':len(paths),'overlap_lines':len(results),'elapsed':time.time()-start}))
