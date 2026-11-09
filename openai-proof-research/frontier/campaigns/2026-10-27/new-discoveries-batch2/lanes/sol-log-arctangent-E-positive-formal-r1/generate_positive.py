import resource,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
for _threadvar in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:
 os.environ[_threadvar]='1'
from pathlib import Path
p=Path(__file__).resolve().parent
out=['import MeanEExpansion','import MeanWeights','import Mathlib.Tactic.Positivity','set_option autoImplicit false','set_option warningAsError true','set_option maxHeartbeats 800000','namespace LogArctangentMean']
def cp(i,j):return f'c{i}_0' if j==0 else (f'(c{i}_1+c{i}_2)' if j==1 else f'c{i}_2')
def w(i,j):return f'Real.cosh (freq{i}*t)' if j==0 else (f'(freq{i}*Real.sinh (freq{i}*t))' if j==1 else f'(freq{i}^2*Real.cosh (freq{i}*t))')
def summ(j):return ' + '.join(f'{cp(i,j)}*{w(i,j)}' for i in range(12))
for j in range(3):
 out.append(f'theorem weighted{j} {{t : ℝ}} (ht : 0 ≤ t) : 0 '+('<' if j==0 else '≤')+' '+summ(j)+' := by')
 out.append('  obtain ⟨'+', '.join(f'ho{i}' for i in range(11))+', hp11⟩ := frequencies_ordered')
 for i in reversed(range(11)):out.append(f'  have hp{i} : 0 < freq{i} := lt_trans hp{i+1} ho{i}')
 for i in range(12):
  pref=' + '.join(cp(k,j) for k in range(i+1))
  if j==1:out.append(f'  have hs{i} : 0 < {pref} := by linarith [prefix_pos_{i}_1, prefix_pos_{i}_2]')
  else:out.append(f'  have hs{i} : 0 < {pref} := prefix_pos_{i}_{j}')
 for i in range(11):
  lemma=['cosh_weight_mono','sinh_weight_mono','square_cosh_weight_mono'][j]
  out.append(f'  have hw{i} : 0 ≤ {w(i,j)}-{w(i+1,j)} := sub_nonneg.mpr ({lemma} (le_of_lt hp{i+1}) (le_of_lt ho{i}) ht)')
 if j==0:out.append('  have hlast := cosh_weight_pos freq11 t')
 elif j==1:out.append('  have hlast := sinh_weight_nonneg (le_of_lt hp11) ht')
 else:out.append('  have hlast := square_cosh_weight_nonneg freq11 t')
 rhs=f'({" + ".join(cp(k,j) for k in range(12))})*{w(11,j)}'+' + '+' + '.join(f'({" + ".join(cp(k,j) for k in range(i+1))})*({w(i,j)}-{w(i+1,j)})' for i in range(11))
 out.append(f'  rw [show {summ(j)} = {rhs} by ring]\n  positivity')
out.append('theorem E_derivative24_pos {t : ℝ} (ht : 0 ≤ t) : 0 < iteratedDeriv 24 E t := by')
out.append('  have h0 := weighted0 ht\n  have h1 := weighted1 ht\n  have h2 := weighted2 ht')
out.append('  have he := E_derivative24 t')
out.append('  have hpos : 0 < ('+summ(0)+') + t*('+summ(1)+') + t^2*('+summ(2)+') := add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg h0 (mul_nonneg ht h1)) (mul_nonneg (sq_nonneg t) h2)')
out.append('  have hid : iteratedDeriv 24 E t / 2 = ('+summ(0)+') + t*('+summ(1)+') + t^2*('+summ(2)+') := by rw [he]; ring')
out.append('  linarith\nend LogArctangentMean')
(p/'formal/MeanEHighPositive.lean').write_text('\n'.join(out)+'\n')
