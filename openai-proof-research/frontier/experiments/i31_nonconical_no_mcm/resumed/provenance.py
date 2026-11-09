from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[4]
S=ROOT/'frontier/sources/i31_nonconical_no_mcm';OUT=S/'resumed'
sha=lambda b:hashlib.sha256(b).hexdigest()
def write(name,x):(OUT/name).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
manifest=json.loads((S/'inputs/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_text())
tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text());index={f['path']:f for f in tree['tree']}
corpus=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus';errors=[];h=hashlib.sha256()
for f in manifest['files']:
 p=corpus/f['path'];b=p.read_bytes();v=sha(b);g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 if v!=f['sha256'] or g!=f['git_blob'] or index.get(f['path'],{}).get('sha')!=g:errors.append(f['path'])
 h.update(f['path'].encode()+b'\0'+v.encode()+b'\n')
roots={f['path'].split('/')[1] for f in tree['tree'] if f['path'].startswith('preprints/') and len(f['path'].split('/'))>=2}
write('inventory-audit.json',dict(pin=manifest['pin'],manuscripts=len(roots),cached_files=len(manifest['files']),errors=errors,path_digest_stream_sha256=h.hexdigest(),full_cache_copied=False))
assert not errors and len(roots)==749 and len(manifest['files'])==9340
patterns=[r'nonconical|non-conical|nonquasihomogeneous',r'Hirzebruch.?Kummer|complete.quadrangle',r'Atiyah.*extension|primitive.*deformation|deformation.*primitive']
scans=[]
for pattern in patterns:
 c=subprocess.run(['rg','--no-ignore','--hidden','-i','-l','--',pattern,str(corpus)],capture_output=True,text=True)
 assert c.returncode in (0,1)
 paths=[str(Path(p).relative_to(corpus)) for p in c.stdout.splitlines()]
 scans.append(dict(pattern=pattern,matched_files=len(paths),paths=paths,limits='Lexical in-place screening, not a claim to have read all matched files.'))
write('corpus-screens.json',scans)
# Freeze resumed control inputs, including the precise original task and parent checkpoint.
inputs=[]
for p in sorted((OUT/'inputs').rglob('*')):
 if p.is_file():
  live=str(p.relative_to(OUT/'inputs'));inputs.append(dict(path=live,frozen=str(p.relative_to(ROOT)),sha256=sha(p.read_bytes()),category='shared_ledger' if live=='frontier/TEN-FINDINGS.md' else 'dependency'))
write('input-manifest.json',inputs)
# Exact theorem environments, with full contracts already read in paper/surface.
pbase=S/'pinned/preprints/A-Complete-Local-Domain-Without-a-Small-Cohen-Macaulay-Module-September-23-2026/build'
uses={'thm:obstruction':'Context: cone obstruction, not applied to a nongraded deformation by fiat.','lem:balance':'Integral Noetherian model, smooth Cartier surface, ample conormal, torsion-free sheaf and positive-rank torsion-free restriction; bounds HN width.','lem:lattice':'Integral Noetherian model with Cartier P2, conormal O(1), torsion-free extension trivial off P2; v>=0.','lem:factor':'Finite smooth-surface projection and torsion-free slope-semistable factor; v upper bound.','prop:surface':'Prime n>=3 complete-quadrangle cover, smooth integral X, ample globally generated H and exact numerical invariants.','lem:cover-smooth':'Local coordinate power maps and degree n^5; used for integral ramification formula.'}
contracts=[]
for filename in ['paper.tex','surface.tex']:
 txt=(pbase/filename).read_text()
 for m in re.finditer(r'\\begin\{(theorem|lemma|proposition)\}(.*?)\\end\{\1\}',txt,re.S):
  labels=re.findall(r'\\label\{([^}]+)\}',m.group())
  for label in labels:
   if label in uses:
    contracts.append(dict(path=str((pbase/filename).relative_to(ROOT)),label=label,start_line=txt[:m.start()].count('\n')+1,end_line=txt[:m.end()].count('\n')+1,exact_statement=m.group(),use=uses[label],statement_sha256=sha(m.group().encode())))
write('source-contracts.json',contracts)
# Passage identities are verified by line slices. Full source proof reads vs bounded literature reads are explicit.
passages=[]
def add(rel,start,end,purpose):
 p=ROOT/rel;lines=p.read_text().splitlines(keepends=True);end=min(end,len(lines));b=''.join(lines[start-1:end]).encode();passages.append(dict(path=rel,start_line=start,end_line=end,purpose=purpose,sha256=sha(b)))
for name in ['paper.tex','surface.tex']:
 p=pbase/name;add(str(p.relative_to(ROOT)),1,len(p.read_text().splitlines()),'Full pinned manuscript/proof read; accepted source, not upstream audit.')
base='frontier/sources/i31_nonconical_no_mcm/literature/'
for name,start,end,purpose in [
 ('pinkham.txt',740,790,'Propositions 2.2-2.3: graded deformation setup'),('pinkham.txt',1071,1260,'Section 3, normal module extension and graded T1 comparison'),('pinkham.txt',1300,1432,'Definition 4.1 and negative-grading theorem; its vanishing hypothesis is not asserted here'),('pinkham.txt',4070,4132,'Proposition 11.2 and proof: positive perturbation rigidity requires no positive T1'),
 ('coughlan-sano.txt',240,285,'Section 3.3: Atiyah extension, inclusion rather than unconditional equality'),('coughlan-sano.txt',344,487,'Section 5: full section ring and weighted normal sequence, conical rigidity hypotheses'),
 ('dff.txt',254,450,'Theorems 2.4-2.5 and Remark 2.7: primitive Hodge component, depth hypothesis distinction'),
 ('bauer-catanese-rigid.txt',48,86,'Theorem 1.2 concerns abstract surface infinitesimal rigidity'),
 ('bauer-catanese-equations.txt',78,166,'Theorems 0.1/0.4/0.5: abstract rigidity and equations with linear syzygies'),
 ('anghel-acm.txt',42,190,'Introduction/Theorem 1.1 and full section-ring distinction: graded obstruction only'),
 ('chen-local.txt',35,172,'Main claim 1.1 and counterexample conditional on claim, numerical K=4H'),
 ('chen-sun.txt',65,125,'Theorem 1.4 and Remark 1.5: optimal extensions across negative divisors'),
 ('artin-notes.txt',1,90,'Introduction distinguishes formal versal objects and effectivity; not used as automatic algebraization')]:add(base+name,start,end,purpose)
add('frontier/sources/i31_nonconical_no_mcm/resumed/literature/demailly-vanishing.txt',146,183,'Section 1, equations (1.4)-(1.5), positive/negative KAN ranges')
comp='preprints/A-singular-normal-affine-surface-with-free-tangent-sheaf-September-23-2026/build/06-algebraization.tex'
p=corpus/comp;txt=p.read_text();pos=txt.index('\\begin{proposition}[Algebraization');end=txt.index('\\end{proposition}',pos)+len('\\end{proposition}')
add(str(p.relative_to(ROOT)),1,80,'Comparison only: finite-determinacy relation-matrix hypotheses')
add(str(p.relative_to(ROOT)),txt[:pos].count('\n')+1,txt[:end].count('\n')+1,'Comparison only: analytic germ and free tangent hypotheses are not imported into I31')
write('read-passages.json',passages)
extra={'path':comp,'url':'https://raw.githubusercontent.com/openai/math/'+manifest['pin']+'/'+comp,'git_blob':index[comp]['sha'],'sha256':sha(p.read_bytes()),'role':'read-only comparison, not a theorem dependency'}
write('additional-pinned-comparison.json',extra)
# Record original files outside the 43 checkpoint files too, without modifying them.
cp=json.loads((ROOT/'frontier/experiments/i31-interrupted-parent-checkpoint.json').read_text());cpnames={x['path'] for x in cp['files']}
extras=[]
for b in [S,ROOT/'frontier/experiments/i31_nonconical_no_mcm']:
 for p in sorted(b.rglob('*')):
  if p.is_file() and 'resumed' not in p.relative_to(b).parts and str(p.relative_to(ROOT)) not in cpnames:extras.append(dict(path=str(p.relative_to(ROOT)),sha256=sha(p.read_bytes())))
write('additional-initial-preservation.json',extras)
print(json.dumps(dict(inventory=9340,manuscripts=749,contracts=len(contracts),passages=len(passages),extra_initial=len(extras),corpus_screen_counts=[x['matched_files'] for x in scans])))
