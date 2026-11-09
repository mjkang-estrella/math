import resource,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
for _threadvar in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:
 os.environ[_threadvar]='1'
from pathlib import Path
import json
from fractions import Fraction as F
p=Path(__file__).resolve().parent
data=json.loads((p.parent/'root-log-arctangent-candidate-r1/exponential-terms.json').read_text())
def r(q):
 q=F(q);return f'(({q.numerator}:ℝ)/{q.denominator})'
def pair(q):return f'({r(q[0])}+{r(q[1])}*d)'
def nm(i,j):return f'expGrid_{"m"+str(-i) if i<0 else i}_{"m"+str(-j) if j<0 else j}'
def coord(i,j):return f'(({i}:ℝ)+({j}:ℝ)*d)'
def expnorm(n,arg):
 if n<0:return f'-( ({-n}:ℕ)*({arg}) )'
 return f'({n}:ℕ)*({arg})'
coords={(int(x['lambda'][0]),int(x['lambda'][1])) for k in ['U','V'] for x in data[k]}
coords|={(1,0),(4,0),(5,0),(0,1),(-1,0),(-4,0),(-5,0),(0,-1)}
out=['import MeanDerivatives','set_option autoImplicit false','set_option warningAsError true','set_option maxHeartbeats 800000','set_option linter.unusedSimpArgs false','set_option linter.unnecessarySeqFocus false','set_option linter.unreachableTactic false','set_option linter.unusedTactic false','namespace LogArctangentMean']
for i,j in sorted(coords):
 def val(n,arg):
  s=f'({arg})^{abs(n)}'
  return '('+s+')⁻¹' if n<0 else s
 out.append(f'theorem {nm(i,j)} (t : ℝ) : Real.exp ({coord(i,j)}*t) = {val(i,"Real.exp t")} * {val(j,"Real.exp (d*t)")} := by')
 out.extend([f'  rw [show {coord(i,j)}*t = {expnorm(i,"t")} + {expnorm(j,"d*t")} by ring, Real.exp_add]', '  simp only [Real.exp_neg, Real.exp_nat_mul]'])
for kind in ['U','V']:
 rhs=' +\n    '.join(pair(x['coefficient'])+f'*Real.exp ({coord(*map(int,x["lambda"]))}*t)' for x in data[kind])
 out.append(f'noncomputable def {kind}Expansion (t : ℝ) : ℝ :=\n    {rhs}')
 out.append(f'theorem {kind}_expansion (t : ℝ) : {kind} t = {kind}Expansion t := by')
 if kind=='U':out.append('  simp only [U, deriv_A, deriv_B, A, B, Ap, Bp, UExpansion, Real.cosh_eq, Real.sinh_eq]')
 else:out.append('  simp only [V, A, B, VExpansion, Real.cosh_eq, Real.sinh_eq]')
 # rws simple exponentials first negative exp to inv; then table expansions
 out.append('  simp only ['+', '.join(nm(i,j) for i,j in sorted(coords))+']')
 # need direct simple exp(4*t) normalized because lhs coord lemma shape (4+0*d) not match
 for n in [4,5]:
  out.append(f'  have hex{n} : Real.exp (({n}:ℝ)*t) = Real.exp t ^ {n} := Real.exp_nat_mul t {n}')
 out.append('  simp only [Real.exp_neg, hex4, hex5]')
 out.append('  field_simp [d_ne, Real.exp_ne_zero]')
 out.append('  ring_nf')
 out.append('  have hc : d^3 = 17*d := by\n    calc d^3 = d^2*d := by ring\n         _ = 17*d := by rw [d_sq]')
 out.append('  simp only [d_sq, hc]\n  ring_nf\n  all_goals simp only [d_sq]; ring')
out.append('end LogArctangentMean')
(p/'formal/MeanExpansion.lean').write_text('\n'.join(out)+'\n')
