"""Pre-seal provenance assembly. Never invoked by the offline verifier."""
from pathlib import Path
import json,hashlib,difflib,subprocess
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i80_geometric_flows_computation_discovery'
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(name,obj): (S/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
def rel(p):return str(p.relative_to(R))
keys={'RV':'Computation-under-Rapidly-Vanishing','ES':'Universal-Computation-with-Eventually','VD':'Velocity-Field-Detection','SP':'Scalar-Potentials','IB':'Incompressible-Box','GS':'Geometric-Programs-for','FS':'Finite-Instructions','PI':'Prefix-Instructions','FP':'A-Fixed-Particle','HY':'Deforming-hypersymplectic','TC':'Taming-implies','RH':'A-closed-Ricci','R4':'Bounded-scalar','RT':'Path-selection-and-an-elliptic'}
domain=json.loads((S/'corpus-domain.json').read_text()); bypath={x['path']:x for x in domain['files']};families={k:sorted((C/'preprints').glob(v+'*')) for k,v in keys.items()}
manifest=[]
for k,dirs in families.items():
 for d in dirs:
  for p in sorted(d.rglob('*')):
   if p.is_file():
    e=dict(bypath[rel(p)]);e.update(family=k,raw_url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['upstream_path']);manifest.append(e)
save('source-manifest.json',manifest)
# Exact version comparisons: byte equality is useful, but neither a diff nor a search is a full read.
versions=[]
for k in ['HY','TC','IB']:
 dirs=families[k];old=next(d for d in dirs if 'September' in d.name);new=next(d for d in dirs if 'October' in d.name)
 for name in sorted({str(p.relative_to(d)) for d in [old,new] for p in d.rglob('*') if p.is_file()}):
  a,b=old/name,new/name; ab=a.read_bytes() if a.exists() else b'';bb=b.read_bytes() if b.exists() else b''
  e=dict(family=k,old=rel(a) if a.exists() else None,new=rel(b) if b.exists() else None,equal=ab==bb,old_sha256=sha(ab),new_sha256=sha(bb))
  if ab!=bb and name.endswith(('.tex','.bib','.md')):
   out=''.join(difflib.unified_diff(ab.decode().splitlines(True),bb.decode().splitlines(True),fromfile=e['old'] or '/dev/null',tofile=e['new'] or '/dev/null'))
   q=S/'version-diffs'/k/name;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(out);e['diff']=rel(q);e['diff_sha256']=sha(q.read_bytes())
  versions.append(e)
save('source-versions.json',versions)
# Conservative retrospective bindings to passages actually displayed and inspected.
# A whole-file flag concerns these bytes, never all files in the manuscript directory.
bindings=[]
def bind(p,start=1,end=None,purpose='source operation inspected',basis='displayed manuscript text'):
 p=Path(p);lines=p.read_bytes().splitlines(keepends=True);end=len(lines) if end is None else end
 assert 1<=start<=end<=len(lines),(p,start,end,len(lines))
 bindings.append(dict(path=rel(p),start=start,end=end,total_lines=len(lines),file_sha256=sha(p.read_bytes()),passage_sha256=sha(b''.join(lines[start-1:end])),purpose=purpose,basis=basis))
def f(k,name,version=None):return next(d for d in families[k] if version is None or version in d.name)/'build'/name
for name in ['main.tex','addressed.tex','alternating.tex','lattice.tex','references.tex']:bind(f('RV',name),purpose='full actual RV source: compiler, scales, all memory variants, analytic class and limits')
bind(f('FS','main.tex'),purpose='full actual direct-solenoidal shear companion, including all intermediate paths and optional schedules')
for name in ['main.tex','introduction.tex','analytic-imports.tex','clocks.tex','recorder-import.tex','interpreter.tex','reciprocal-template.tex','body.tex']:bind(f('GS',name),purpose='full displayed mathematical text of direct-solenoidal geometric companion')
bind(f('ES','main.tex'),purpose='full eventual-stationary and periodic constructions; compiler/routing gap in first broad output re-read separately')
for name in ['main.tex','analytic.tex','main-result.tex','bcs-clocks.tex','bcs-clock-options.tex','bcs-prefix.tex','bcs-expanded.tex','scalar-stages.tex']:bind(f('SP',name),purpose='scalar-potential companion: precise theorem, comparison, clock and prefix/suspension operations')
# bcs-scalar conservatively bind only the untruncated operation ranges after the initial heading.
bind(f('SP','bcs-scalar.tex'),15,139,purpose='delayed recorder, full rectangles, compact scalar-potential motion and loading')
bind(f('VD','main.tex'),purpose='full detector statements, force restrictions and analytic reduction')
for name in ['analytic-tools.tex','analytic-appendix.tex']:bind(f('FP',name),purpose='lower uniqueness operation and exact scope of periodic solenoidal projection')
for name in ['01-introduction.tex','02-construction.tex','03-geometry.tex','04-cap.tex','05-reaction.tex','06-barriers.tex']:bind(f('RH','sections/'+name),purpose='full actual high-dimensional Ricci construction and quantitative proof operations')
bind(f('RH','references/bibliography.tex'),purpose='primary provenance of construction inputs')
bind(f('R4','sections/01-introduction.tex'),purpose='dimension-four hypothesis and exact flow/static interfaces; body not fully read')
for name in ['sections/01-introduction.tex','sections/11-endpoint.tex']:bind(f('HY',name,'October'),purpose='hypersymplectic theorem and complete endpoint construction; companion bodies not fully read')
bind(f('HY','sections/05-families.tex','October'),1,150,purpose='actual compatible-family smooth right-inverse operation')
# Primary claims are verified against bounded exact passages, not all bibliographic antecedents.
for name,ranges,purpose in [
 ('stolarski-v1',[(1,230),(580,675),(8190,8445)],'actual v1 main scope and formal cap matching, not a proved unique cap limit'),
 ('beltrami-v3',[(60,145),(1230,1425)],'Euclidean infinite energy and tape-bounded torus/viscous scope'),
 ('dgmp-published',[(155,290)],'UPC April 15 2026 DRAFT theorem A: deformed metric and Hodge viscosity'),
 ('gavrilov-v1',[(1,315),(345,390)],'compact Euler localization and nonsmooth core circle; no rigid-rotation gate imported'),
 ('clv-v1',[(1,160)],'localizable Grad-Shafranov construction and nonlinear compact-pressure precedent'),
 ('brandolese-meyer',[(1,704)],'full paper: energy isotropy, higher-moment polynomial divisibility, persistence conditions and discrete symmetry examples'),
 ('okabe-brandolese',[(145,225)],'Theorem 2.1 matrix divergence-form force, small initial data, and exact meaning of rapid dissipation')]:
  p=S/'primary'/(name+'.txt')
  for a,b in ranges:bind(p,a,min(b,len(p.read_bytes().splitlines())),purpose=purpose,basis='displayed pdftotext -layout extraction from retained primary PDF')
for p,a,b in [(R/'frontier/iterations/i27-geometric-analysis-discovery.md',80,141),(R/'frontier/iterations/i74-relative-symplectic-packing.md',80,88)]:bind(p,a,b,purpose='historical parked scope; no prior deduction imported into new proof')
save('passages.json',bindings)
# Separate complete file inventory from actual read coverage, with remaining ranges explicit.
coverage=[]
for e in manifest:
 p=R/e['path']
 if p.suffix not in ['.tex','.bib']:continue
 n=len(p.read_bytes().splitlines());covered=set()
 for b in bindings:
  if b['path']==e['path']:covered.update(range(b['start'],b['end']+1))
 missing=[];start=None
 for i in range(1,n+2):
  if i<=n and i not in covered:
   if start is None:start=i
  elif start is not None:missing.append([start,i-1]);start=None
 coverage.append(dict(path=e['path'],family=e['family'],lines=n,bound_lines=len(covered),unbound_ranges=missing))
save('read-coverage.json',dict(status='INCOMPLETE_FULL_COMPANION_READ_GATE',note='The binding is conservative. Unbound means no retained positive claim of complete semantic reading. Full-tree search and hash verification are not reading.',files=coverage))
refs=[]
for name in ['frontier/iterations/i27-geometric-analysis-discovery.md','frontier/iterations/i74-relative-symplectic-packing.md','frontier/sources/i72_graph_probability_discovery/inventory.json','frontier/sources/i72_graph_probability_discovery/corpus-domain.json']:
 p=R/name;refs.append(dict(path=name,sha256=sha(p.read_bytes()),bytes=p.stat().st_size))
save('immutable-references.json',refs)
searches=json.loads((S/'searches.json').read_text())
pat=r'compact.{0,50}(solenoidal|divergence.free)|solenoidal.{0,50}compact|pressure.{0,40}compact|compact.{0,40}pressure|swirl|concentric.{0,30}(shell|annul)|harmonic.moment'
p=subprocess.run(['rg','--no-ignore','-n','-i','--',pat,str(C)],capture_output=True,text=True);assert p.returncode in [0,1]
out=p.stdout.replace(str(C)+'/', '');q=S/'pressure-scope-search.txt'
# Preserve the earlier absolute-path variant before canonicalizing.
if q.exists() and q.read_text()!=out:(S/'pressure-scope-search-initial.txt').write_bytes(q.read_bytes())
q.write_text(out)
searches=[e for e in searches if e['name']!='pressure-scope'];searches.append(dict(name='pressure-scope',pattern=pat,flags=['--no-ignore','-n','-i'],output=rel(q),lines=len(out.splitlines()),sha256=sha(q.read_bytes())))
save('searches.json',searches)
print(json.dumps(dict(source_files=len(manifest),bindings=len(bindings),coverage_bound=sum(x['bound_lines'] for x in coverage),coverage_lines=sum(x['lines'] for x in coverage),status='INCOMPLETE_FULL_COMPANION_READ_GATE')))
