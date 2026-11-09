from pathlib import Path
import gzip,resource,signal,json
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(200,200));signal.alarm(220)
L=Path(__file__).resolve().parent
# Read generator without running it.
ns={};exec((L/'generate.py').read_text().split('cells,gs=data(10,10,1)')[0],dict(__file__=str(L/'generate.py')),ns)
# Standalone balanced total lookup; all branches return natural bytes.
def tree(vals,x):
 if len(vals)==1:return str(vals[0])
 m=len(vals)//2
 return f'(if {x} < {m} then {tree(vals[:m],x)} else {tree(vals[m:],f"({x}-{m})")})'
raw=gzip.decompress((L/'inputs/compression/steiner-7-5-0.bin.gz').read_bytes());n=24;full=16383
for count in [16,256,1024]:
 # Consecutive proper nonempty submasks of full; symmetry pairs s < complement.
 a=[tree(list(raw[s*n:(s+1)*n]),'v.val') for s in range(1,count+1)]
 b=[tree(list(raw[(full^s)*n:(full^s+1)*n]),'v.val') for s in range(1,count+1)] if False else [tree(list(raw[(full^s)*n:((full^s)+1)*n]),'v.val') for s in range(1,count+1)]
 s='''import FiniteBridge
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LargeBenchmark
'''
 s+=f'def left (s : Fin {count}) (v : Fin 24) : ℕ := '+tree(a,'s.val')+'\n'
 s+=f'def right (s : Fin {count}) (v : Fin 24) : ℕ := '+tree(b,'s.val')+'\n'
 s+='def full (v : Fin 24) : ℕ := '+tree(list(raw[full*n:(full+1)*n]),'v.val')+'\n'
 s+=f'theorem checked : ∀ s : Fin {count}, ∀ v : Fin 24, full v + 1 ≤ left s v + right s v := by decide\nend LargeBenchmark\n'
 name=f'Large{count}'
 (L/'dev'/f'{name}.lean').write_text(s)
