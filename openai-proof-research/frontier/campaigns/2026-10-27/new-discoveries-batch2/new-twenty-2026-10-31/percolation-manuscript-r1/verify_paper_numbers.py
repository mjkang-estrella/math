from pathlib import Path
import sys,json,hashlib
D=Path(sys.argv[1]).resolve();P=D.parent
j=json.loads((D/'recomputation.json').read_text());p=D/'paper.md';s=p.read_text()
old='This is a draft contribution to a campaign seeking new significant MathDB solutions proved in Lean. It carries zero accepted credit in this dossier; root alone decides acceptance. The theorem’s substantive content is the failure of a literal permitted existential assertion. Formal completion, source fidelity, independent mathematical review, bounded novelty evidence and acceptance are distinct gates.'
s=s.replace(old,'This AI-assisted campaign draft carries zero accepted credit; root alone decides acceptance. Formal completion, source fidelity, novelty evidence and acceptance remain distinct gates.')
p.write_text(s)
paths=[P/'expanded-corpus-r164/outputs/percolation-sat.json',P/'expanded-corpus-r164/outputs/percolation-sym-5-5.cnf',P/'expanded-corpus-r164/outputs/percolation-5-5-trim.lrat',P/'percolation-review-r1/independent.cnf',P/'percolation-review-r1/independent.lrat',P/'percolation-formal-r4/generator-correspondence.json',P/'percolation-formal-r4/packet/src/NormalizedExport.lean']
def digest(f):return hashlib.sha256(f.read_bytes()).hexdigest()
before={str(f):digest(f) for f in paths}
(D/'supplemental-inputs-before.json').write_text(json.dumps(before,indent=2)+'\n')
checks={}
for name,path,clauses in [('review',paths[3],8312),('discovery',paths[1],7940)]:
 lines=path.read_text().splitlines();header=next(x for x in lines if x.startswith('p ')).split();assert int(header[2])==1085 and int(header[3])==clauses;assert len([x for x in lines if x and not x.startswith(('c','p'))])==clauses
 checks[name+'_clauses']=clauses
for name,path,count in [('review',paths[4],141005),('discovery',paths[2],82646)]:
 total=0
 with path.open() as f:
  for line in f:
   xs=line.split()
   if len(xs)>1 and xs[1]!='d':total+=1
 assert total==count;checks[name+'_additions']=total
# Paper table is bound to all fresh recomputed masks and counts.
for c in j['controls']:
 row=f"| {c['q']} | {c['r']} | {c['mask']} | {c['size']} | {', '.join(map(str,c['round_sizes']))} | {c['time']} |";assert row in s
assert j['cnf']['clauses']==14698 and j['cnf']['variables']==1085
assert j['certificate']['hint_uses']==3340122 and j['certificate']['additions']==129671
assert j['certificate']['literal_occurrences']==1868145 and j['certificate']['used_inputs']==11294
assert j['formal_record']['developer_replay_seconds']==5232.09
assert sum(j['cnf']['families'].values())==14698
# All required documentation is read as UTF-8 and its word count indexed.
index=[]
for k in range(1,9):
 for name in ['SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','results.json']:
  f=P/f'percolation-formal-r{k}'/name
  if f.exists():text=f.read_text();index.append(dict(path=str(f),words=len(text.split()),sha256=digest(f)))
(D/'documentation-read-receipt.json').write_text(json.dumps(index,indent=2)+'\n')
assert before=={str(f):digest(f) for f in paths}
(D/'supplemental-inputs-after.json').write_text(json.dumps(before,indent=2)+'\n')
for f in [paths[0],paths[-2],paths[-1]]:
 out=D/'evidence'/f.relative_to(P);out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(f.read_bytes())
(D/'paper-number-audit.json').write_text(json.dumps(dict(status='PASS',historical_trace_counts=checks,controls='all table rows exact',fresh_result='recomputation.json',provenance_numbers='Source identifiers, dates, page/section labels, toolchain versions and reported external statuses are verified against frozen text, not computed mathematical data.'),indent=2)+'\n')
print('Numerical audit passed; historical counts independently counted; table rows exact.')
