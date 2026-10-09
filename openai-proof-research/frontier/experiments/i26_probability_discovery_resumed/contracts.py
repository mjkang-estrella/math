"""Exact statement inventory and explicitly selected proof-read passages."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i26_probability_discovery_resumed';P=S/'pinned/preprints'
sha=lambda b:hashlib.sha256(b).hexdigest()
contracts=[]
for p in sorted(P.rglob('*.tex')):
 text=p.read_text()
 for m in re.finditer(r'\\begin\{(theorem|proposition|lemma|corollary|hypothesis|assumption)\}.*?\\end\{\1\}',text,re.S):
  snippet=m.group();contracts.append(dict(path=str(p.relative_to(R)),start_line=text[:m.start()].count('\n')+1,end_line=text[:m.end()].count('\n')+1,environment=m[1],labels=re.findall(r'\\label\{([^}]+)\}',snippet),text=snippet,sha256=sha(snippet.encode())))
(S/'statement-contracts.json').write_text(json.dumps(contracts,indent=2)+'\n')
# These ranges record passages actually inspected, not a claim to have read every inventoried statement.
spec={
 'Cardys-formula':{'00-introduction.tex':[(1,80)]},
 'A-Pivotal-Amplitude':{'00-introduction.tex':[(1,55)]},
 'From-critical-crossings':{'01-introduction.tex':[(1,270)],'05-expansion.tex':[(1,220),(392,419)],'06-sewing.tex':[(1,86),(106,125)],'07-identification.tex':[(30,36),(130,169)]},
 'Logarithmic-Relative':{'introduction.tex':[(1,110)],'marked.tex':[(1,123),(209,294)],'readout.tex':[(433,475)]},
 'Quenched-SLE3-limits-for-general':{'introduction.tex':[(1,134)]},
 'Gaussian-free-field-limits-of-weighted-integer-Lipschitz-heights-October':{'01-introduction.tex':[(1,125)],'07-limit.tex':[(700,805)]},
 'The-Gaussian-free-field-limit-of-integer-Lipschitz-heights-with-two-arc-boundary-data-October':{'01-introduction.tex':[(1,270)],'02-spin.tex':[(1,130)],'03-cuts.tex':[(223,291)],'04-moments.tex':[(173,250)],'08-boundary.tex':[(1,101),(297,446)],'09-limits.tex':[(1,193),(298,410)],'10-gaussian.tex':[(1,290)]},
 'Uniform-real-Lipschitz-surfaces-on-the-triangular-lattice-October':{'paper.tex':[(30,145)],'trace.tex':[(1,167)],'interface.tex':[(829,884),(1000,1101),(1379,1447)]},
 'The-Gaussian-free-field-limit-of-the-balanced-six-vertex':{'01-introduction.tex':[(30,105)]}}
passages=[]
def add(p,lo,hi,kind):
 a=p.read_text().splitlines(keepends=True);hi=min(hi,len(a));b=''.join(a[lo-1:hi]).encode();passages.append(dict(path=str(p.relative_to(R)),start_line=lo,end_line=hi,kind=kind,sha256=sha(b),text=b.decode()))
for key,files in spec.items():
 d=next(p for p in P.iterdir() if p.name.startswith(key))
 for name,ranges in files.items():
  p=next(d.rglob(name))
  for lo,hi in ranges:add(p,lo,hi,'pinned-read-passage')
literature={'schramm':[(631,679)],'ss-discrete':[(74,136)],'ss-continuum':[(421,478)],'miller':[(61,122)],'glazman-manolescu':[(160,205)],'glazman-lammers':[(140,163)],'sixvertex':[(390,405),(525,589)],'vanneuville':[(132,150),(264,282)],'poisson-spectra':[(342,367)],'davis-cardy':[(1,110)],'dotsenko':[(1,110)]}
for key,ranges in literature.items():
 p=S/'literature'/(key+'.txt')
 if p.exists():
  for lo,hi in ranges:add(p,lo,hi,'primary-read-passage')
(S/'read-passages.json').write_text(json.dumps(passages,indent=2)+'\n')
# Dates are exact abstract-page submission-history strings; metadata does not prove theorem scope.
versions=[]
for p in sorted((S/'literature').glob('*-abs.html')):
 t=p.read_text();a=t.find('Submission history');b=t.find('Full-text links',a);h=re.sub('<[^>]+>',' ',t[a:b]);h=re.sub(r'\s+',' ',h).strip();versions.append(dict(path=str(p.relative_to(R)),submission_history=h))
(S/'literature-versions.json').write_text(json.dumps(versions,indent=2)+'\n')
print(json.dumps(dict(statement_contracts=len(contracts),read_passages=len(passages),primary_versions=len(versions))))
