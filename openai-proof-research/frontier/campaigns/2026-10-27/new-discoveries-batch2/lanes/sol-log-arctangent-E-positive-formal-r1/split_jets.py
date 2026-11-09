import resource,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
for _threadvar in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:
 os.environ[_threadvar]='1'
from pathlib import Path
p=Path(__file__).resolve().parent/'formal'
for block in range(3,6):
 s=(p/f'MeanJets{block}.lean').read_text()
 head=s.split('theorem E_jet_')[0]
 chunks=s[len(head):].split('theorem E_jet_')[1:]
 for chunk in chunks:
  n=int(chunk.split(' ')[0])
  (p/f'MeanJet{n}.lean').write_text(head+'theorem E_jet_'+chunk.replace('end LogArctangentMean\n','')+'end LogArctangentMean\n')
 (p/f'MeanJets{block}.lean').write_text('\n'.join(f'import MeanJet{n}' for n in range(block*4,block*4+4))+'\n')
