from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parents[3]; S=ROOT/'frontier/sources/i23_kinetic_connected_fluctuations'
sha=lambda b:hashlib.sha256(b).hexdigest()
def save(name,data):(S/name).write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
manifest=json.loads((S/'pinned-manifest.json').read_text());idx=json.loads((S/'inputs/sources/preprints-tree.json').read_text());tree={x['path']:x for x in idx['tree']}
assert not idx.get('truncated',False)
for x in manifest['files']:
 assert x['git_blob']==tree[x['path']]['sha'];b=(S/'corpus'/x['path']).read_bytes();assert sha(b)==x['sha256']
names=sorted({x['path'].split('/')[1] for x in idx['tree'] if x['path'].startswith('preprints/') and len(x['path'].split('/'))>1})
save('inventory-screen.json',dict(manuscripts=len(names),keywords=['boltzmann','particle','kinetic','fluctuation','gas-'],matches=[n for n in names if any(w in n.lower() for w in ['boltzmann','particle','kinetic','fluctuation','gas-'])],limitation='Name screen plus actual H/P companion introductions and references; not an exhaustive full-text novelty proof.'))
contracts=[]
for x in manifest['files']:
 if not x['path'].endswith('.tex'):continue
 t=(S/'corpus'/x['path']).read_text()
 for m in re.finditer(r'\\begin\{(assumption|theorem|maintheorem|maincorollary|proposition|lemma|corollary|definition|remark)\}.*?\\end\{\1\}',t,re.S):
  contracts.append(dict(path=x['path'],start_line=t[:m.start()].count('\n')+1,end_line=t[:m.end()].count('\n')+1,labels=re.findall(r'\\label\{([^}]+)\}',m.group()),text=m.group(),sha256=sha(m.group().encode())))
save('statement-contracts.json',dict(note='Mechanical index; extraction is not a claim to have read every statement.',contracts=contracts))
h=next(p.name for p in (S/'corpus/preprints').iterdir() if p.name.startswith('Hard-sphere'))
p=next(p.name for p in (S/'corpus/preprints').iterdir() if p.name.startswith('The-Boltzmann'))
reads=[('H','01-introduction.tex',50,210,'Exact ensemble, normalization and finite-dimensional scope'),('H','02-initial-target.tex',38,83,'Initial Gaussian law and cumulants'),('H','04-cluster-expansion.tex',83,163,'Non-overcounted forest/MST extraction'),('H','04-cluster-expansion.tex',437,584,'Marked resummation and factorial component identity'),('H','04-cluster-expansion.tex',664,733,'Bounded complexity removal and cumulant expansion'),('H','06-sharp-asymptotics.tex',1,448,'Sharp scale, merger charts, factorials and normalized summation'),('H','07-gaussian-limit.tex',362,445,'Ordinary/factorial cumulant identity and Gaussian moments'),('H','08-transfer.tex',1,73,'Exact centering requires expectation transfer'),('P','00-introduction.tex',1,220,'Full regular-interval hypotheses and strongest source scope'),('P','01-preliminaries.tex',13,220,'Potential, initial law, exact flow, insertion'),('P','01-preliminaries.tex',224,435,'Actual scattering and incoming flux interfaces'),('P','01-preliminaries.tex',475,500,'Uniform spatial Gaussian source envelopes'),('P','01-preliminaries.tex',653,660,'Limits of isolated-scattering conclusions'),('P','02-cell-expansion.tex',1,350,'Whole-component Boolean identity, factorial normalization, all-displayed factorization'),('P','03-centering.tex',1,180,'Singleton pattern centering and reference-tree construction'),('P','03-centering.tex',390,708,'Layer recurrence, exact cancellation, ownership and pin-forest distinction'),('P','04-history-estimates.tex',1,195,'Whole-component source-energy and augmented-volume ledger'),('P','04-history-estimates.tex',195,490,'Intact multibody pinning and original-parent estimate'),('P','04-history-estimates.tex',583,683,'Quantitative and qualitative parameter discards'),('P','05-exposure.tex',865,1020,'Fixed-size original-chart vanishing and its unnormalized scope'),('P','06-closure.tex',266,420,'Strong completed-history summability and limit order'),('P','06-closure.tex',630,764,'Actual-process and remainder bounds')]
passages=[]
for kind,file,a,b,purpose in reads:
 path='corpus/preprints/'+(h if kind=='H' else p)+'/build/sections/'+file
 lines=(S/path).read_text().splitlines();b=min(b,len(lines));txt='\n'.join(lines[a-1:b])+'\n'
 passages.append(dict(kind=kind,path=path,start_line=a,end_line=b,purpose=purpose,text=txt,sha256=sha(txt.encode())))
for file,a,b,purpose in [('lebihan.txt',395,452,'Potential and Gibbs ensemble'),('lebihan.txt',570,607,'Theorem 1 covariance and restrictions'),('pss.txt',389,412,'Repulsive class and angular momentum duration bound'),('pss.txt',3055,3084,'Stable Hypothesis 1 prime'),('pss.txt',3243,3280,'Stable short-time Theorem 1 prime'),('bgss.txt',475,550,'Exact centering and short-time Gaussian process theorem'),('cluster.txt',310,339,'Whole-trajectory polymer interpretation'),('cluster.txt',534,556,'Short-time convergent cluster bound'),('bgss_equilibrium.txt',301,350,'Equilibrium use and full Gaussian theorem'),('lebihan_hard_v1.txt',190,246,'Hard-sphere equilibrium covariance statements')]:
 path='literature/'+file;lines=(S/path).read_text().splitlines();txt='\n'.join(lines[a-1:b])+'\n';passages.append(dict(kind='literature',path=path,start_line=a,end_line=b,purpose=purpose,text=txt,sha256=sha(txt.encode())))
save('reading-contracts.json',dict(note='Exact retained passages actually used in this assignment; accepted-source proofs not audited.',passages=passages))
versions=[]
for q in (S/'literature').glob('*.html'):
 text=q.read_text();hist=re.search(r'\[Submitted on.*?</div>',text,re.S)
 versions.append(dict(file=str(q.relative_to(S)),submission_text=re.sub('<[^>]+>','',hist.group()) if hist else None,version_tags=sorted(set(re.findall(r'\[v(\d+)\]',text)))))
save('literature/versions.json',versions)
print(json.dumps({'pinned_files':len(manifest['files']),'inventory_count':len(names),'statement_contracts':len(contracts),'read_passages':len(passages)}))
