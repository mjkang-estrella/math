"""Build exact source contracts and passage locators from frozen local bytes."""
from pathlib import Path
import json,re,hashlib,shutil
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i25_matching_entropy_improvement_resumed'
def put(name,obj): (S/name).write_text(json.dumps(obj,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
contracts=[]
for row in json.loads((S/'pinned-manifest.json').read_text()):
 p=R/row['local_path'];s=p.read_text()
 for mat in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}(?:\[[^\]]*\])?',s):
  end=s.find('\\end{'+mat.group(1)+'}',mat.end())
  assert end>=0;end+=len('\\end{'+mat.group(1)+'}');block=s[mat.start():end]
  labels=re.findall(r'\\label\{([^}]+)\}',block)
  contracts.append(dict(path=row['local_path'],kind=mat.group(1),labels=labels,start=mat.start(),end=end,sha256=sha(block.encode()),text=block))
put('source-contracts.json',contracts)
# Exact ranges actually read; entire decisive source proofs retained as passages.
manifest=json.loads((S/'pinned-manifest.json').read_text());byname={Path(r['path']).name:r['local_path'] for r in manifest}
passages=[]
def passage(path,start,end,purpose):
 p=R/path;lines=p.read_text().splitlines(keepends=True);end=min(end,len(lines));b=''.join(lines[start-1:end]).encode();passages.append(dict(path=path,start_line=start,end_line=end,sha256=sha(b),purpose=purpose,text=b.decode()))
for name,purpose in [('01-introduction.tex','Full scope, original coefficient, comparison and source algorithm limitation'),('02-polytope.tex','Full gluing, face, no-tight-cut rank branch and fixed-coordinate proof'),('03-entropy.tex','Full continuity, exponential law, covariance trace and components proofs'),('04-consequences.tex','Scalar budget and structural count comparison'),('05-weighted.tex','Full weighted variational interface and its computational disclaimer'),('10-examples.tex','Full Klee face construction, entropy and coefficient obstruction'),('appendix-b.tex','Full normalized inverse-covariance nonlinear proof')]:
 # For introduction/consequences we read relevant prefixes rather than claim full algorithm section.
 end={'01-introduction.tex':175,'04-consequences.tex':145}.get(name,100000)
 passage(byname[name],1,end,purpose)
passage(byname['appendix-a.tex'],1,310,'Laminar and quotient-space alternatives and fractional reductions')
fpras=next(r['local_path'] for r in manifest if 'Fully-Polynomial' in r['path'])
passage(fpras,123,153,'Unweighted FPRAS theorem and uniform sampling interface')
passage(fpras,330,360,'Weighted intermediate spaces versus the stated input theorem')
put('read-passages.json',passages)
passages=[]
L=S/'literature'
for name,a,b,purpose in [('gurvits',90,245,'Theorem 2.2 weighted bipartite permanent inequality and its full proof'),('cube-ideal',878,978,'Current v2 laminar rank proof, matching count theorem and staircase example'),('entropy-optimization',145,285,'Generalized weighted counting oracle, interior condition, primal-dual discussion'),('entropy-optimization',510,635,'Formal Lemma 2.3 and Theorems 2.6, 2.7, 2.8, with exact oracle and interiority hypotheses'),('girth-bethe',185,254,'Conditioning/good-vertex information-flow mechanism'),('girth-bethe',460,486,'Theorem 3.1 exact bipartite entropy upper-bound scope'),('dong-jain',1,58,'Theorem 1.1 weighted bipartite permanent approximation')]:
 passage(str((L/(name+'.txt')).relative_to(R)),a,b,purpose)
put('primary-passages.json',passages)
# Source corpus manifest is a small metadata dependency, not a corpus copy.
p=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json';q=S/'inputs/corpus-manifest.json';shutil.copyfile(p,q)
rows=json.loads((S/'inputs.json').read_text());row=dict(path=str(p.relative_to(R)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()),snapshot=str(q.relative_to(R)))
if not any(r['path']==row['path'] for r in rows):rows.append(row)
put('inputs.json',rows)
c=json.loads(q.read_text());files=c['files'];base=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
for row in files:assert sha((base/row['path']).read_bytes())==row['sha256']
tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text());assert not tree['truncated'];manuscripts={r['path'].split('/')[1] for r in tree['tree'] if r['path'].startswith('preprints/')}
put('corpus-screen.json',dict(manuscripts=len(manuscripts),text_files_verified=len(files),query='matching.{0,40}entropy|entropy.{0,40}matching|Bethe|cube.ideal',flags='rg -uuu -l -i; .tex, .md, .txt',hits_path=str((S/'corpus-matching-hits.txt').relative_to(R)),scope='Bounded text search only, not full reading of corpus; irrelevant lexical/vendor hits are retained. Selected source and companion proof passages read separately.',corpus_manifest_sha256=sha(q.read_bytes())))
put('candidate-contract.json',dict(status='candidate proof; not independently reviewed',premise_commit='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',quantifiers='For every finite undirected loopless labelled multigraph G on 2m>=2 vertices with a perfect matching, every x in P(G), and every vertex v',conclusion='F_G(x)-H_G(x) <= (3/2) sum_{e not incident to v} -(1-x_e) log(1-x_e)',boundary='0 log 0=0; arbitrary zero and one means, parallel edges and disconnected graphs included',bridge=['Exact rooted budget additivity at every tight odd-cut split','Positive-maximum induction excludes all nontrivial tight cuts','Rooted covariance trace 0>=d-s+m+c(m-1), with d>=s-2m at the remaining maximum','Four-vertex multigraph base and epsilon endpoint'],not_claimed=['optimality of 3/2','polynomial prescribed-mean sampling','independent proof acceptance','significance acceptance','worldwide priority','count increment']))
print('contracts',len(contracts),'source passages',len(json.loads((S/'read-passages.json').read_text())),'primary passages',len(passages),'corpus',len(files),'manuscripts',len(manuscripts))
