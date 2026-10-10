"""Preparation only; writes only I136-owned evidence. Not used by offline verifier."""
from pathlib import Path
import hashlib,json,re,sys
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i136_birational_positivity_discovery'
sha=lambda b:hashlib.sha256(b).hexdigest()
def j(p):return json.loads((R/p).read_text())
def save(name,x):(S/name).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
assert not (S/'seal.json').exists()
old=[('i112_inverse_boundary_discovery','6b0e58e12bbc8af8e4ed3f66c7cb6d38963da6fce6370c4f3e840b91cae1a42e'),('i115_physical_elasticity_continuation','e038e926e30d7505ecb9cd398f785a525d529799dd79a3803c472cc3ab800432'),('i118_physical_quotient_angular','1256b9c7c8371486805557acddadfc2d851cb26268297155c989b1ff56d4169d'),('i121_physical_transfer_bound','4cf2dca95899c5d68c02f87161e83230665b2c2532301848934f5dde52193278'),('i124_fractal_incidence_discovery','0c47be17de45a72348387eccd304cc62a529e3c692ef5c5b26f979166f3e665f'),('i127_diagonal_pinned_distance','d917b10cbe80dfc969c6a3dce949ab6ee5968baa91ef76da01e6f9b3bb4c3cad'),('i130_spectral_harmonic_discovery','02f7953cec355a2cca7b0c3e9ad7b2d116bd3f9b52ac62103545873db63d3000'),('i133_fixed_metric_harmonic_growth','41e1f7496a66e034fabd1d95995dd5c8e7be198532194b6c0e06fd2871a20346')]
ledgers=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'];refs={};anchors=[];passages=[];lex=[]
def add(p,h):
 assert p not in ledgers
 assert not re.search(r'/(?:i|iteration)(134|135)[-_]',p),p
 if p in refs:assert refs[p]==h,(p,refs[p],h)
 refs[p]=h
for name,h in old:
 base='frontier/sources/'+name;sp=base+'/seal.json';assert sha((R/sp).read_bytes())==h
 add(sp,h);seal=j(sp);inv=j(base+'/inventory.json')
 assert set(seal['sha256'])==set(inv['owned_paths'])
 for p,hh in seal['sha256'].items():add(p,hh)
 for x in j(base+'/immutable-references.json'):add(x['path'],x['sha256'])
 for p in j(base+'/read-manifest.json')['passages']:
  add(p['local'],p['file_sha256']);passages.append(p)
 lp=base+'/lexical-search.json'
 if (R/lp).exists():lex.append(lp)
 anchors.append({'base':base,'seal':sp,'sha256':h,'inventory':base+'/inventory.json'})
# Manual reads already displayed in this session, distinct from lexical matches.
man=j('frontier/sources/i136_birational_positivity_discovery/read-manifest.json')
# A truncated attempted full range is retained as an attempt, not credited; recovered chunks are credited.
attempts=[x for x in man['passages'] if x['local'].endswith('/H-reduction.tex') and x['start']==1 and x['end']==767]
man['passages']=[x for x in man['passages'] if x not in attempts]
base='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
manual=[(base+'Fujitas-freeness-conjecture-September-23-2026/build/main.tex',1,216),(base+'A-Three-Dimensional-Counterexample-to-Integer-Degree-Harmonic-Dimension-Comparison-September-26-2026/build/sections/geometry.tex',1,352),(base+'A-Three-Dimensional-Counterexample-to-Integer-Degree-Harmonic-Dimension-Comparison-September-26-2026/build/sections/transfer.tex',273,409),('frontier/iterations/i02-crossfield.md',1,100),('frontier/reviews/i02-crossfield-r2.md',1,81),('frontier/iterations/i02-hodge-construction.md',1,50),('frontier/iterations/i02-hodge-cylinder-r2.md',1,35),('frontier/iterations/i02-arithmetic.md',1,60),('frontier/iterations/i27-geometric-analysis-discovery.md',1,100),('frontier/iterations/i70-symplectic-geometry-discovery.md',1,48),('frontier/iterations/i74-relative-symplectic-packing.md',1,100),('frontier/iterations/i98-complex-kahler-discovery.md',1,100),('frontier/iterations/i102-relative-k3-oka-construction.md',1,70),('sources/CONTENTS.md',1085,1146),('sources/CONTENTS.md',1654,1686),('AGENTS.md',1,13)]
for p,lo,hi in manual:
 b=(R/p).read_bytes();ls=b.decode().splitlines();hi=min(hi,len(ls));man['passages'].append(dict(local=p,start=lo,end=hi,line_count=len(ls),file_sha256=sha(b),convention='splitlines',passage_sha256=sha('\n'.join(ls[lo-1:hi]).encode()),reading='manual display; retroactive exact binding'))
# Deduplicate exact passage bindings, not lexical representations.
seen=set();out=[]
for p in man['passages']:
 key=(p['local'],p['start'],p['end'])
 if key not in seen:seen.add(key);out.append(p)
man['passages']=out;save('read-manifest.json',man)
for p in out:
 if not p['local'].startswith('frontier/sources/i136_birational_positivity_discovery/'):add(p['local'],p['file_sha256'])
for x in j('frontier/sources/i136_birational_positivity_discovery/input-freeze.json'):
 if x['path'] not in ledgers:add(x['path'],x['sha256'])
paths=sorted({p for p,lo,hi in manual if p.startswith('frontier/iterations/') or p.startswith('frontier/reviews/')})
expr=r'(?i)(seshadri|nagata|fujita|complement|nef|jet|relative|very general|substantial)';rx=re.compile(expr);hits=[]
for p in paths:
 add(p,sha((R/p).read_bytes()))
 for i,line in enumerate((R/p).read_text().splitlines(),1):
  mm=list(rx.finditer(line))
  if mm:hits.append(dict(path=p,splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
save('overlap-search.json',dict(expression=expr,paths=paths,results=hits,matched_lines=len(hits),occurrences=sum(len(x['spans']) for x in hits)))
save('inheritance.json',dict(anchors=anchors,immutable=[{'path':p,'sha256':h} for p,h in sorted(refs.items())],inherited_passages=passages,lexical_records=lex,live_ledgers=ledgers,scope='Flat byte/passage validation; never execute inherited verifiers or diagnostics'))
save('reading-notes.json',dict(mandatory_context_completed_before_audit=True,context_lines=4499,uncredited_truncated_attempts=attempts,display_failures=['Initial full JSON display truncated; decoded unique stream subsequently read in all 4499 lines, initial 135-230 recovered.','Combined complement/source display truncated; complete H-reduction reread 1-250,251-520,521-767, introduction reread.','Several broad overlap/ledger displays truncated: credited only explicit bounded passages in read-manifest; all lexical hits recorded but not counted as full semantic reading.','rg --files without --no-ignore returned no cached files; corrected invocation used.','arxiv HTML 1202.6662v3 returned 404; current metadata identifies v2, which was retrieved successfully.'],unread=['Earlier Fujita minimizer machinery','Deep complement threshold/pinning machinery beyond the complete reductions','Siu full proof','Full external Ito internal semigroup chain','Other Chen equivalence implications'],primary_versions={'ito':2,'chen':5,'siu':'version of record 2026-05-15'},extraction='HTMLParser retains MathML visible text and TeX annotations; whitespace collapsed per nonempty line; no PDF re-extraction this round'))
patterns={'birational_positivity':r'(?i)(fujita|nagata|seshadri|klt.{0,24}complement|cartier.{0,24}section)','mixed_jet_operations':r'(?i)(weighted.{0,45}(?:jet|sesha|nef)|(?:jet|interpolat).{0,45}(?:weight|multiplicit)|(?:complement|cartier).{0,45}(?:simultaneous|prescribed|finite set))'}
# Preparation makes one flat domain traversal and validates originals while recording new lexical data.
domain=j('frontier/sources/i112_inverse_boundary_discovery/search-domain.json');result={k:[] for k in patterns};compiled={k:re.compile(v) for k,v in patterns.items()}
for x in domain:
 b=(R/x['local']).read_bytes();o=b if x['local']==x['original_local'] else (R/x['original_local']).read_bytes()
 assert sha(b)==x['sha256'] and sha(o)==x['original_sha256']
 assert hashlib.sha1(b'blob '+str(len(o)).encode()+b'\0'+o).hexdigest()==x['git_sha']
 for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
  for k,rx in compiled.items():
   mm=list(rx.finditer(line))
   if mm:result[k].append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
save('lexical-search.json',dict(patterns=patterns,results=result,counts={k:dict(matched_lines=len(v),occurrences=sum(len(x['spans']) for x in v)) for k,v in result.items()}))
selected=[x for x in domain if any(z in x['path'] for z in ['Fujitas-freeness','Nagatas-Conjecture','Maximal-Seshadri','Maximal-Multipoint-Seshadri','Maximal-multipoint-Seshadri','Bounded-klt-complements','Uniform-Cartier-sections'])]
save('selected-source-bindings.json',[dict(x,url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']) for x in selected])
print(json.dumps(dict(immutable=len(refs),inherited_passages=len(passages),new_passages=len(out),lexical_counts={k:len(v) for k,v in result.items()},selected_bindings=len(selected))))
