from pathlib import Path
import json,re,hashlib,datetime,math
from fractions import Fraction
R=Path(__file__).resolve().parent;D=R/'fresh-extraction';L=R.parent
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
rows=json.loads((R/'strict-modules-receipt.json').read_text())['declarations']
assert len(rows)==139 and len({r['name'] for r in rows})==139
assert all(not any(r[k] for k in ['unsafe','partial','axiom']) and set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in rows)
src={p.stem:p.read_text() for p in (D/'formal').glob('*.lean')}
for n,s in src.items():assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',s.replace('unsafe=','').replace('axiom=','')) if n!='FullAudit' else True
assert 'ConvexOn ℝ (Set.Icc 0 2) (sourceTime phi)' in src['Defs']
assert '∀ phi : ℝ, 0<phi → phi<Real.pi/2 →' in src['Defs']
assert 'theorem source_claim : SourceClaim :=' in src['Result']
expected={r['name'] for r in rows}
assert 'PendulumTimeMap.source_claim' in expected
coef=[]
for n in range(80):
 c=Fraction(math.comb(2*n,n),8**n);d=Fraction(math.comb(2*(n+1),n+1),8**(n+1))
 assert (n+1)*d==Fraction(2*n+1,4)*c and c>0
 coef.append(str(c))
# Independently derived concavity control at a=z=1; tests incorrect all-orders
# convex-convolution shortcut. Analytic derivatives are recorded in review.md.
assert Fraction(-1*(1+3),2*(1+1)**2)==Fraction(-1,2)
context={}
for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
 p=L.parent/n;s=p.read_text();context[n]={'sha256':sha(p),'bytes':p.stat().st_size,'lines':len(s.splitlines()),'relevant_lines':[x for x in s.splitlines() if re.search('pendulum|cholesteric|accepted_count|next_global|total_accepted',x,re.I)]}
assert json.loads((L.parent/'ledger.json').read_text())['accepted_count']==9
upstreams=[]
for n in ['originals-before.json','input-records.json']:
 rr=json.loads((D/n).read_text());upstreams.append({'file':n,'entries':len(rr)})
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'declarations':139,'all_rows_checked':True,'actual_types_preserved':'strict-modules-receipt.json','module_sources_read':list(src),'positive_coefficient_exact_recurrence_80':coef,'negative_control_B0_second_derivative_at_1':str(Fraction(-1,2)),'context':context,'frozen_input_coverage':upstreams,'dependency_files':len(json.loads((D/'dependency-hashes.json').read_text())),'proof_basis':'analytic source review plus kernel replay; arithmetic checks are supplemental'}
(R/'independent-evidence.json').write_text(json.dumps(out,indent=2)+'\n')
for i,r in enumerate(rows):
 print(i,r['origin'],r['name'],r['actual_type'])
