import resource,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
for _threadvar in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:
 os.environ[_threadvar]='1'
from pathlib import Path
p=Path(__file__).resolve().parent
vals={10:37847040,12:19891322880,14:5550283554816,16:1162696473968640,18:206947471161556992,20:33226670114812723200,22:4978839848478924865536}
for block in range(6):
 out=['import MeanEExpansion','set_option autoImplicit false','set_option warningAsError true','set_option maxHeartbeats 800000','set_option linter.unusedSimpArgs false','set_option linter.unnecessarySeqFocus false','set_option linter.unusedTactic false','set_option linter.unreachableTactic false','namespace LogArctangentMean']
 for n in range(block*4,block*4+4):
  out.append(f'theorem E_jet_{n} : iteratedDeriv {n} E 0 = {vals.get(n,0)} := by')
  out.append('  rw [E_eq_evalExpList, iteratedDeriv_evalExpList, expListJet_map]')
  if n>=2:
   out.append(f'  have hn (q : ExpQuadratic) : q.jet {n} = q.jetFormula {n-2} := q.jet_formula {n-2}')
  out.append('  simp only [EList, pairExp, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, evalExpList, '+('hn, ExpQuadratic.jetFormula' if n>=2 else 'ExpQuadratic.jet, ExpQuadratic.step')+', ExpQuadratic.eval, List.map_map, Function.comp_def]')
  out.append('  norm_num [Real.exp_zero]')
  out.append('  dsimp ['+', '.join(f'{v}{i}' for i in range(12) for v in ['freq','u','v'])+']')
  out.append('  ring_nf')
  if n>=2:out.append('  all_goals simp only ['+', '.join(f'd_power_{k}' for k in range(2,27))+']; ring')
 out.append('end LogArctangentMean')
 (p/f'formal/MeanJets{block}.lean').write_text('\n'.join(out)+'\n')
