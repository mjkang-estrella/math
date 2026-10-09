#!/usr/bin/env python3
"""Build source/primary contracts from already retained bytes; never edits shared inputs."""
import hashlib,json,re,subprocess
from html.parser import HTMLParser
from pathlib import Path
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i19_fresh_structural_discovery'
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[]
 def handle_data(self,d):self.out.append(d)
for p in sorted((S/'literature').glob('*')):
 if p.suffix=='.html':
  parser=Text();parser.feed(p.read_text());p.with_suffix('.txt').write_text(' '.join(' '.join(parser.out).split()))
 elif p.suffix=='.pdf':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
contracts=[]
pat=re.compile(r'\\begin\{(theorem|lemma|proposition|corollary)\}(?:\[[^\]]*\])?[\s\S]*?\\end\{\1\}')
for a in json.loads((S/'pinned-manifest.json').read_text()):
 p=S/'pinned'/a['path']
 if p.suffix!='.tex':continue
 t=p.read_text()
 for m in pat.finditer(t):
  labels=re.findall(r'\\label\{([^}]+)\}',m[0]);contracts.append(dict(path=a['path'],labels=labels,start_line=t[:m.start()].count('\n')+1,end_line=t[:m.end()].count('\n')+1,text=m[0],sha256=sha(m[0].encode())))
dump(S/'theorem-contracts.json',contracts)
wanted={
 'A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026':{
  'specht-tools.tex':[(1,100)],'dominance.tex':[(1,None)],'band-quotient.tex':[(1,None)],'path-band.tex':[(1,None)],'completion.tex':[(1,None)],'introduction.tex':[(1,None)]},
 'Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026':{
  '01-introduction.tex':[(1,None)],'02-graphs.tex':[(145,228)],'03-reordering.tex':[(1,260),(620,650),(760,795)],'04-walls.tex':[(1,240)],'05-triangle.tex':[(1,260),(525,640)],'06-witness.tex':[(1,None)],'07-completion.tex':[(1,None)]},
 'Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026':{'balance.tex':[(1,365)]},
 'Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026':{'introduction.tex':[(1,None)],'setup.tex':[(1,None)]},
 'A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026':{'main.tex':[(3080,3134)]}}
loc=[]
for a in json.loads((S/'pinned-manifest.json').read_text()):
 p=S/'pinned'/a['path'];family=a['path'].split('/')[1];ranges=wanted.get(family,{}).get(p.name,[])
 for start,end in ranges:
  lines=p.read_text().splitlines(keepends=True);end=min(len(lines),end or len(lines));b=''.join(lines[start-1:end]).encode();loc.append(dict(path=a['path'],start_line=start,end_line=end,sha256=sha(b),role='statement/proof passage used in screen; remaining retained files are companion context'))
dump(S/'read-locators.json',loc)
# Specific primary passages, exact offsets in deterministic text extraction.
spec={
 'bessenrodt-bowman.txt':[('refined_target','Conjecture 10.2 .','Conjecture 10.3 .'),('band_split','Theorem 7.11 .','There are some further closely related cases'),('sign_location','Corollary 6.2 .','We want to build on Theorem 6.1'),('semigroup','Proposition 2.5 .','3. The class functions')],
 'davison-mandel.txt':[('general_Lefschetz','Conjecture 1.4 .','1.3. Dequantization'),('acyclic_contract','Theorem 3.14 .','3.3.4. An application of positivity')],
 'shareshian-wachs-v2.txt':[('target','Conjecture 1.3.','Conjecture 1.3 applies')],
 'dyer-muller.txt':[('host_switch_obstruction','2. Ergodicity of the switch chain.','Lemma 2.2.'),('slow_mixing','4. Slow mixing of the switch chain.','5. Deciding')],
 'foster-tom-v2.txt':[('known_K_chain_scope','Abstract.','1. Introduction')]}
primary=[]
for name,items in spec.items():
 t=(S/'literature'/name).read_text()
 for label,start,end in items:
  i=t.find(start)
  if i<0:
   print('NO START',name,start);continue
  j=t.find(end,i+len(start))
  if j<0 or j-i>20000:j=min(len(t),i+6000)
  text=t[i:j];primary.append(dict(path=str(Path('frontier/sources/i19_fresh_structural_discovery/literature')/name),label=label,start_offset=i,end_offset=j,text=text,sha256=sha(text.encode())))
dump(S/'primary-contracts.json',primary)
tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text());manuscripts=sorted({a['path'].split('/')[1] for a in tree['tree'] if a['path'].startswith('preprints/')});dump(S/'inventory-screen.json',dict(truncated=tree['truncated'],entries=len(tree['tree']),manuscript_count=len(manuscripts),manuscripts=manuscripts,terms=['Saxl','Tensor-Squares','Chromatic','Switch-Chain','Perfect-Matchings'],matching_paths=[a for a in tree['tree'] if any(s in a['path'] for s in ['Saxl','Tensor-Squares','Chromatic','Switch-Chain','Perfect-Matchings'])]))
queries=[
'Bessenrodt Bowman Splitting Kronecker squares staircase symmetric exterior conjecture 10.2',
'Shareshian Wachs e unimodality chromatic quasisymmetric functions conjecture 2026',
'switch chain weighted graphs prescribed degree sequence arbitrary edge weights slow mixing',
'"Splitting Kronecker squares" "2202.03066"',
'"quantum theta" "Lefschetz" acyclic Davison Mandel',
'"switch chain" "edge weights" mixing',
'site.arxiv.org "Strong positivity for quantum theta bases"',
'site.arxiv.org "Splitting Kronecker squares"',
'"refined Saxl" conjecture symmetric exterior 2026',
'"Saxl" "symmetric" "band"',
'"chromatic" "e-unimodality" 2026 proof',
'"switch" "Metropolis" "edge weights" perfect matchings']
dump(S/'literature/queries.json',dict(date='2026-10-09',provider='web.run',queries=queries,raw_results_retained_for=['queries 7-8: web-catalog-search.json','queries 9-12: web-final-search.json'],note='Earlier query strings reconstructed from exact tool arguments; their raw responses were read in-session but not retained. Primary bytes and contracts, not snippets, ground the report.'))
print(json.dumps(dict(source_contracts=len(contracts),read_ranges=len(loc),primary_contracts=len(primary),manuscripts=len(manuscripts))))
