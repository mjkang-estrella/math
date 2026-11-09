import resource,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
for _threadvar in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:
 os.environ[_threadvar]='1'

from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
for f in ['generate.py','generate_expansion.py','generate_E.py','generate_positive.py','generate_jets.py','split_jets.py']:
 subprocess.run([sys.executable,str(p/f)],check=True,timeout=45)
for n in range(21,24):
 f=p/f'formal/MeanJet{n}.lean'
 s=f.read_text().replace('norm_num [Real.exp_zero]','norm_num [Real.exp_zero, neg_pow]\n  ring_nf')
 if n%2:s=s[:s.index('  dsimp [freq')]+'end LogArctangentMean\n'
 f.write_text(s)
