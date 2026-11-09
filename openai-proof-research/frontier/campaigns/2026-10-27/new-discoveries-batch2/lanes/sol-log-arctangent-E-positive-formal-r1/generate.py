import resource,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
for _threadvar in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:
 os.environ[_threadvar]='1'
from pathlib import Path
import json
from fractions import Fraction as F
p=Path(__file__).resolve().parent
table=json.loads((p.parent/'root-log-arctangent-candidate-r1/exponential-terms.json').read_text())
cert=json.loads((p.parent/'root-log-arctangent-certificate-r2/checks.json').read_text())['success']['rows']
def rat(x):
 q=F(x)
 return f'({q.numerator}:ℝ)' if q.denominator==1 else f'(({q.numerator}:ℝ)/{q.denominator})'
def pair(x):return f'({rat(x[0])}+{rat(x[1])}*d)'
def get(kind,lam):return next(x['coefficient'] for x in table[kind] if x['lambda']==lam)
out=['import MeanAnalyticDefs','set_option autoImplicit false','set_option warningAsError true','set_option linter.unusedSimpArgs false','set_option linter.unnecessarySeqFocus false','set_option linter.unreachableTactic false','set_option maxRecDepth 4096','set_option maxHeartbeats 800000','namespace LogArctangentMean']
for n in range(2,27):
 rhs=f'({17**(n//2)}:ℝ)'+(' * d' if n%2 else '')
 if n==2: proof='exact d_sq'
 elif n==4: proof='rw [show 4 = 2+2 from rfl, pow_add, d_sq]; norm_num'
 else: proof=f'rw [show {n} = {n-2}+2 from rfl, pow_add, d_sq, d_power_{n-2}]; ring' if n>3 else 'calc d^3 = d^2*d := by ring\n       _ = 17*d := by rw [d_sq]'
 out.append(f'theorem d_power_{n} : d^{n} = {rhs} := by\n  {proof}')
for i,row in enumerate(cert):
 l=row['frequency']
 out.extend([f'noncomputable def freq{i} : ℝ := {pair(l)}',f'noncomputable def u{i} : ℝ := {pair(get("U",l))}',f'noncomputable def v{i} : ℝ := {pair(get("V",l))}'])
 for j,expr in enumerate([f'freq{i}^22*(u{i}*freq{i}^2+24*v{i}*freq{i}+1104*u{i})',f'freq{i}^22*(v{i}*freq{i}+94*u{i})',f'2*freq{i}^22*u{i}']):
  out.append(f'noncomputable def c{i}_{j} : ℝ := {expr}')
out.append('theorem frequencies_ordered : '+' ∧ '.join([f'freq{i+1} < freq{i}' for i in range(11)]+['0 < freq11'])+' := by\n  have hlo := d_bounds.1\n  have hhi := d_bounds.2\n  dsimp ['+', '.join(f'freq{i}' for i in range(12))+']\n  constructor <;> try linarith')
# use repeat constructor and linarith
out[-1]=out[-1].replace('constructor <;> try linarith',"(repeat' apply And.intro) <;> linarith")
for i,row in enumerate(cert):
 for j,ab in enumerate(row['prefix']):
  lhs=' + '.join(f'c{k}_{j}' for k in range(i+1))
  if i==0:
   expr=f'{lhs}'
   simpdefs=f'c{i}_{j}, freq{i}, u{i}, v{i}'
  else:
   expr=f'({pair(cert[i-1]["prefix"][j])}) + c{i}_{j}'
   simpdefs=f'c{i}_{j}, freq{i}, u{i}, v{i}'
  out.append(f'theorem prefix_value_{i}_{j} : {lhs} = {pair(ab)} := by')
  if i>0:out.append(f'  rw [show {lhs} = ({" + ".join(f"c{k}_{j}" for k in range(i))}) + c{i}_{j} by ring, prefix_value_{i-1}_{j}]')
  out.extend([f'  dsimp [{simpdefs}]','  ring_nf'])
  if F(row['frequency'][1]):out.append('  simp only ['+', '.join(f'd_power_{n}' for n in range(2,27))+']; ring')
  bound=rat(F(ab[0])+F(ab[1])*(F(41,10) if F(ab[1])>=0 else F(21,5)))
  out.append(f'theorem prefix_pos_{i}_{j} : 0 < {lhs} := by\n  rw [prefix_value_{i}_{j}]\n  have hlo := d_bounds.1\n  have hhi := d_bounds.2\n  linarith')

out.append('end LogArctangentMean')
(p/'formal/MeanFiniteCertificate.lean').write_text('\n'.join(out)+'\n')
