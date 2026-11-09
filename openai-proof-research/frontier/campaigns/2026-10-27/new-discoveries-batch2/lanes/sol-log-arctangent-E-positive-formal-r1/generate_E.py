import resource,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
for _threadvar in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:
 os.environ[_threadvar]='1'
from pathlib import Path
import re
p=Path(__file__).resolve().parent
out=['import MeanExpansion','import MeanFiniteCertificate','import ExpPolynomial','set_option autoImplicit false','set_option warningAsError true','set_option maxHeartbeats 800000','set_option linter.unusedSimpArgs false','namespace LogArctangentMean']
out.append('theorem exp_mul_nat (x : ℝ) (n : ℕ) : Real.exp (x*n) = Real.exp x^n := by rw [mul_comm, Real.exp_nat_mul]')
out.append('noncomputable def EList : List ExpQuadratic := [⟨0,-87/68,0,-87/34⟩] ++ '+ ' ++ '.join(f'pairExp freq{i} u{i} v{i}' for i in range(12)))
out.append('theorem E_eq_evalExpList : E = evalExpList EList := by\n  funext t\n  simp only [E, U_expansion, V_expansion, UExpansion, VExpansion, EList, pairExp, evalExpList, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, ExpQuadratic.eval]')
out.append('  dsimp ['+', '.join(f'{v}{i}' for i in range(12) for v in ['freq','u','v'])+']')
names=re.findall(r'theorem (expGrid_\w+)',(p/'formal/MeanExpansion.lean').read_text())
out.append('  simp only ['+', '.join(names)+']')
for i in range(12):
 import json
 row=json.loads((p.parent/'root-log-arctangent-certificate-r2/checks.json').read_text())['success']['rows'][i]
 a,b=map(int,row['frequency'])
 name=f'expGrid_{"m"+str(-a) if a<0 else a}_{"m"+str(-b) if b<0 else b}'
 coord=f'(({a}:ℝ)+({b}:ℝ)*d)'
 out.append(f'  have hneg{i} : Real.exp (-{coord}*t) = (Real.exp ({coord}*t))⁻¹ := by rw [neg_mul, Real.exp_neg]')
out.append('  simp only ['+', '.join(f'hneg{i}' for i in range(12))+']')
out.append('  simp only ['+', '.join(names)+']')
out.append('  norm_num')
out.append('  field_simp [Real.exp_ne_zero]')
out.append('  ring')
out.append('theorem evalExpList_append (xs ys : List ExpQuadratic) (t : ℝ) : evalExpList (xs++ys) t = evalExpList xs t + evalExpList ys t := by simp [evalExpList]')
out.append('theorem expListJet_append (xs ys : List ExpQuadratic) (n : ℕ) : expListJet n (xs++ys) = expListJet n xs ++ expListJet n ys := by simp only [expListJet_map, List.map_append]')
out.append('theorem E_derivative24 (t : ℝ) : iteratedDeriv 24 E t / 2 =\n  '+ ' +\n  '.join(f'(c{i}_0*Real.cosh (freq{i}*t)+t*(c{i}_1+c{i}_2)*freq{i}*Real.sinh (freq{i}*t)+t^2*c{i}_2*freq{i}^2*Real.cosh (freq{i}*t))' for i in range(12))+' := by')
out.append('  rw [E_eq_evalExpList, iteratedDeriv_evalExpList]')
out.append('  simp only [EList, expListJet_append, evalExpList_append, pairExp_derivative24]')
out.append('  simp only [expListJet_map, List.map_cons, List.map_nil, evalExpList, List.sum_cons, List.sum_nil, ExpQuadratic.jet24, ExpQuadratic.jetFormula, ExpQuadratic.eval]')
out.append('  norm_num\n  dsimp ['+', '.join(f'c{i}_{j}' for i in range(12) for j in range(3))+']\n  ring')
out.append('end LogArctangentMean')
(p/'formal/MeanEExpansion.lean').write_text('\n'.join(out)+'\n')
